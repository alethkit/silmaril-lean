# Seeded execution for checked Python modules

`Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded`
consumes the checked instruction stream from the ordinary module-call
compiler. Callers opt in by passing a `Core.Module.SeededCall.Namespace`
to `Seeded.run`. Module bindings and builtin bindings remain separate
throughout execution. The ordinary module runner has its own entry point.
[Seeded entry](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Run/Seeded/Defs.lean)
· [Closed host-free calls](python-module-seeded-call.md)

The seeded profile admits integer literals, global reads, single-name
assignments, truth assertions, and fixed-positional calls to the closed
descriptors. A call can discard its result, bind it after success, or use
it as a direct assertion condition. An argument may itself be a named
call with literal or name operands. The runner saves the outer callee
first, evaluates arguments from left to right, and invokes the saved
value only after every argument returns. An instruction failure keeps
its incoming module bindings and skips the remaining instructions.
[Python evaluation order](https://docs.python.org/release/3.12.13/reference/expressions.html#evaluation-order)

For message-free `assert not test`, the seeded runner uses the same
operands as a positive assertion.
It evaluates the operand once, then checks for a false value. A
failed operand read keeps its defined error, and a truthy operand
raises an empty `AssertionError`. Both paths preserve earlier module
bindings.

Scalar equality evaluates its left and right operands in order and uses
the ordinary module's integer and Boolean comparison. The Boolean result
can be bound, tested, or used in a later scalar comparison. Boolean
literals are admitted inside equality. Equality on `None`, exception
classes, and helper values is unsupported. Arithmetic and standalone
Boolean literals remain outside the seeded operand profile.

The runner handles the checked stream at module instruction granularity.
User function publication, ordinary closure callbacks, and constructing
exception instances lie outside the seeded profile. There is no host
callable or reflection interface. The closed dispatcher handles both inner
and outer calls.
`Observation.calls` records evaluated argument calls in order, then the
outer receipt if all inputs resolved. A missing outer name emits no
nested-call receipts. Each receipt carries the result and the error
caught by that call's expectation helper, including a typed integer-pair
payload on a caught assertion. Raised Python errors and unsupported
operations are distinct outcomes.

`run_preserves_builtins` proves that execution preserves the supplied
builtin table. `failing_instruction` gives the exact residual and trace
on failure. `observeArguments_iff` relates the runner to ordered argument
evaluation rules with a first-failure rule. `observeNestedCall_missing`
and `observeNestedCall_failedArguments` give the exact failure outcomes
before outer dispatch. `SeededCall.runObserved_result` connects the
call receipt's result to the checked closed evaluator, and
`Expectation.caught_iff` states when a typed error appears in the catch field.
[Runner theorems](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Run/Seeded/Thms.lean)

## Corpus replay handoff

Use the same raw inputs, hashes, and historical selection as the ordinary
module-call replay. Compile each input once with
`ModuleEntry.Functions.Run.compile`. Record compilation rejection before
choosing the runner. Keep the ordinary result and the explicit seed
profile in separate ledger fields. The seeded entry reports unsupported
instructions and calls separately from Python errors. Only count a
completion/output match within the admitted seeded profile.

For the hash-pinned assertion case, run the checked stream with
`Namespace.empty`, `Seeded.legacySeed .builtin`, and
`Seeded.legacySeed .preamble` independently. The two legacy seeds each
provide the `AssertionError` class. The builtin seed installs the two
helpers in the builtin table and the preamble seed installs them in the
module. The preamble seed is a projection onto the bindings used by this
call. The original CPython runner executes the full preamble separately.
Compare the completion, output, and specified residual user bindings
under each profile.

The upstream raw case at revision
`b7ff99372dd24845cf84e58c96b877f15764b276` has SHA-256
`822abc163f457af8784c41c08cef152ecbb1266bb9704197292944386bc3dd79`.
The legacy SOS report records successful completion with empty output
and 21846 transitions. A compatibility rerun of the upstream runner on
CPython 3.9.25 with typed-ast 1.5.5 recorded successful completion with
empty output and 22146 transitions. The recorded transition totals are
separate from the observable completion and output comparison. The
seeded Lean runner's typed call receipts represent module call outcomes.
[Public case](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/lambda-py/python-reference/exceptions/assertion-error.py)
· [Archived SOS result](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/reports/sospython.json#L3931)
· [Legacy CPython invocation](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/evaluation/run_cpython.py#L50)

The three nested-call cases from the same audit set match CPython under
each equivalent restricted namespace. All raise `NameError` with no
changes to user bindings.

| Pinned case | First missing name in empty namespace | First missing name in either supplied seed |
| --- | --- | --- |
| `bool-callable.py` | `___assertIs` | `___assertIs` |
| `bool-int.py` | `___assertEqual` | `int` |
| `bool-isinstance.py` | `___assertIs` | `___assertIs` |

The full preamble also supplies `___assertIs` and `___assertIsNot` and
runs with stock builtins. The restricted seed has neither helper, and
does not model the `int`, `callable`, or `isinstance` calls or the Boolean
and type operands used by these rows. The restricted-namespace errors
are separate from normal completion under the full preamble.
[Pinned Boolean cases](https://github.com/koehlma/rigorous/tree/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/lambda-py/python-reference/bool)

The two pinned scalar equality rows now complete normally in the ordinary
runner and every restricted seeded namespace. `testassign1.py` retains
`x = 5`. `testintegers1.py` leaves user bindings empty and reaches its
final negated assertion. Both have empty call traces. The replay checks
these rows and the other seven admitted inputs against CPython, with the
namespace and outcome recorded for each profile.
[Pinned equality rows](https://github.com/koehlma/rigorous/tree/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/k-python/programs)

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms +Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Thms'
python3 -I tests/languages/python/source-module-entry/check_seeded_run.py
python3 -I tests/languages/python/source-module-entry/check_seeded_run.py --upstream /path/to/pinned/rigorous
```

The independently authored fixtures exercise the empty control, both
seed placements, shadowing, caught and unmatched assertions, and
the two missing-exception diagnostics. Nested-call fixtures check
callee and argument error precedence, receipt order, assertion delivery,
and residual bindings. Unsupported fixtures run only in Lean. The
optional upstream check validates the revision and raw-file hashes
before emitting the same inputs under the three namespace configurations.
[Fixtures](../../tests/languages/python/source-module-entry/check_seeded_run.py)
