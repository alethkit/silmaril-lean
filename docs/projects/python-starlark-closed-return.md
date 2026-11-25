# Python and Starlark closed return agreement

A shared `Body Int` represents the return expression of an already entered
zero-argument function. Its tree contains exact signed integer literals,
addition and floor division. The tree preserves grouping and operand order.
The Python elaborator produces a `Python.Core.Body`. The Starlark elaborator
produces a `Starlark.SourceStmt` and passes it to function-body resolution in
the empty global and parameter context. Each language keeps its own syntax,
arithmetic rules and control semantics.
[Shared syntax and observations](../../Silmaril/Languages/PythonStarlark/ClosedReturn/Defs.lean)

## Observation contract

`Agree` compares the same observation predicate in both directions for each
shared integer body. Python's predicate uses `HasOpSem.May`, `NoEntry`,
reachable policy UB and infinite operational traces. Starlark's predicate
uses source resolution and `Exec`. The proof also characterizes it through
the public `runFunctionBody` entry point. The two projections match an
integer return and the defined error for a zero divisor in floor division.
Initial rejection, reachable profile UB and divergence have distinct
tags. Other Starlark errors and returns and a Python trap retain separate
observations. The contract omits internal steps, exception messages and
stack traces. [Agreement theorems](../../Silmaril/Languages/PythonStarlark/ClosedReturn/Thms.lean)

All shared integer bodies are admitted in the Python arithmetic profile
and resolve in Starlark. Python's decreasing transition budget rules out
infinite traces. Starlark's scalar big-step rules have a finite derivation
for every resolved statement and frame by adequacy of the structurally
recursive denotation. This pins the absence of divergence to the two
present models. An extension with loops or host effects will need an
explicit account of divergent runs and additional observations.

## Boolean operands

The Boolean adapter uses the same expression tree with integer and
Boolean literals. An arithmetic operation is required at the root, so a
Boolean literal always occurs as an operand. The Python adapter lowers
unshadowed `True` and `False` to their built-in arithmetic values, 1 and 0,
and uses the integer core for the resulting operations. The Starlark
adapter emits an ordinary read of the appropriate predeclared name and
resolution preserves its Boolean value.

Both elaborations are admitted for `return True + 1`. The Python
operational model returns 2 and the Starlark operational model reports a
dynamic addition type error. The scope of the Python adapter is built-in
Boolean operands of these arithmetic operators. A bare Boolean return,
user-defined numeric dispatch, source parsing and name resolution in
nonempty contexts require further models. The regression also swaps two
Starlark operands capable of different failures to exercise which failure
is observed first. [Lean regressions](../../tests/languages/python-starlark/ClosedReturn.lean)

The Python baseline is the 3.12.13 Language Reference and Standard Library
Reference. The Standard Types HTML has SHA-256
`dd18748757c1fb19ab03068a9adfd8df2c66c2a1b6fb89d168723cede69ab242`.
The Starlark baseline is the core language specification at
`c0af0ea03dc90d3bbc021394b693e6957cc15030`, whose raw Markdown has SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Python Boolean type](https://docs.python.org/release/3.12.13/library/stdtypes.html#boolean-type-bool)
· [Python evaluation order](https://docs.python.org/release/3.12.13/reference/expressions.html#evaluation-order)
· [Starlark Booleans](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#booleans)
· [Starlark integers](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#integers)

## Checks

Run with the pinned repository toolchain and both language models available.

```sh
make check CHECK_TARGETS='+Silmaril.Languages.PythonStarlark.ClosedReturn.Thms +Silmaril.Languages.Python.Core.Thms +Silmaril.Languages.Starlark.Checks'
lake env lean -DautoImplicit=false -DwarningAsError=true --run tests/languages/python-starlark/ClosedReturn.lean
```

Only the resolution proof uses the implementation equations of the candidate
Starlark resolver. A public lemma characterizing resolution for no-name
expressions and predeclared literals would remove that proof dependency.
