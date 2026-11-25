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
descriptors. Calls also accept exact Boolean literals as positional operands.
A call can discard its result, bind it after success, or use
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
A module-level function can be published as the same empty-capture
function value used by the ordinary runner. Publication checks its code
reference and layout in the compiled ordinary table. The binding shadows
builtin fallback, and publication leaves every other binding and the
ordinary heap intact. A missing key or mismatched layout reports the
exact module `publicationFault`. `run_publication` and
`run_publication_fault` give the exact continuation or residual state.

A direct named call to the typed exception-expectation helper can run a
function published earlier in the same module execution. The callback
must have zero positional parameters and receive zero arguments.
The runner uses the ordinary call and delivery path with the current
module-first namespace and shared heap. Integers, Booleans, `None`, and
ordinary functions can cross the lookup boundary. A read of a seed-only
class, helper or builtin descriptor is unsupported, including when the expectation would
have caught a genuinely missing name.

After a matching defined exception, the helper returns `None` and records
the caught error. An unmatched exception propagates. A normal callback
return raises the helper's configured missing-exception diagnostic.
An executor fault or a live prefix at the explicit callback fuel limit
stops module execution with its own outcome and retains the current heap.
The default limit is 1000 ordinary transitions per callback. Direct
ordinary module calls through the seeded runner, ordinary callbacks in
nested helper calls, and constructing exception instances remain outside
the seeded profile. The closed dispatcher still handles closed callbacks.

`Observation.calls` records evaluated argument calls in order, then the
settled outer receipt. A missing outer name emits no nested-call receipts.
Each receipt carries the result and any caught error, including typed
integer-pair and Boolean-pair payloads on closed assertions and the empty payload on an
ordinary assertion. Executor faults and exhausted prefixes emit no
settled helper receipt.

`run_preserves_builtins` proves that execution preserves the supplied
builtin table. `failing_instruction` gives the exact residual and trace
on failure. `observeArguments_iff` relates the runner to ordered argument
evaluation rules with a first-failure rule. `observeNestedCall_missing`
and `observeNestedCall_failedArguments` give the exact failure outcomes
before outer dispatch. `invokeCall_published`, `callback_path`, and
`callback_delivers` connect callback admission, the ordinary labelled path,
and the existing expectation delivery rules with the precise residual heap.
`SeededCall.runObserved_result` and `Expectation.caught_iff` characterize
closed execution and the catch payload.
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

The full preamble supplies `___assertIs` and `___assertIsNot` and runs with
stock builtins. The table uses the exception-helper projection
`legacySeed`. The separate opt-in `legacyBoolIntSeed` adds the typed
`int(bool)` builtin and the mixed integer/Boolean `___assertIsNot`
helper. The builtin uses builtin fallback in both placements, and the
helper uses the selected harness namespace.

In both Boolean-integer placements, `bool-int.py` completes normally
in Lean and CPython with no changes to user bindings. Lean records eight
calls in order, including the exact integer conversion results and
`None` from each assertion helper. The other two rows still raise
`NameError` for `___assertIs` in those projected namespaces.

`legacyBoolCallableSeed` independently extends `legacySeed` with
`___assertIs` in the selected harness namespace and stock `callable`
and `len` in builtin fallback. `bool-callable.py` completes normally
in both placements with no changes to user bindings. Its four receipts
carry `True`, `None`, `False`, and `None` in order. In this projection,
`bool-int.py` reaches the missing `int` and `bool-isinstance.py`
reaches the missing `isinstance`. The separate CPython full-preamble
run with stock builtins completes `bool-callable.py` quietly.

`legacyBoolIsinstanceSeed` independently extends `legacySeed` with
`___assertIs` in the selected harness namespace and stock `isinstance`,
`bool` and `int` in builtin fallback. The pinned `bool-isinstance.py`
completes in both placements with an empty user-binding delta. Its six
instance checks return `True` four times, then `False` twice. Each
paired identity assertion returns `None`. In this projection the
`bool-callable.py` control reaches the missing `callable` and
`bool-int.py` reaches the missing `___assertIsNot`. The full pinned
preamble on stock CPython 3.13.5 completes the instance case quietly.
[Pinned Boolean cases](https://github.com/koehlma/rigorous/tree/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/lambda-py/python-reference/bool)

The two pinned scalar equality rows now complete normally in the ordinary
runner and every restricted seeded namespace. `testassign1.py` retains
`x = 5`. `testintegers1.py` leaves user bindings empty and reaches its
final negated assertion. Both have empty call traces. The replay checks
these rows and the other seven admitted inputs against CPython, with the
namespace and outcome recorded for each profile.
[Pinned equality rows](https://github.com/koehlma/rigorous/tree/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/k-python/programs)

The pinned `assert-silent.py` case publishes `failing_function` under
all three restricted profiles. The empty profile then raises
`NameError("___assertRaises")` during callee lookup. In both supplied
profiles, the runner and CPython execute the callback and catch its
empty assertion error. The helper returns `None`, and the function
binding survives in every profile.
[Pinned publication row](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/lambda-py/python-reference/exceptions/assert-silent.py)

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms +Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/module-seeded-call/Publication.lean
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/module-seeded-call/Callback.lean
python3 -I tests/languages/python/source-module-entry/check_seeded_run.py
python3 -I tests/languages/python/source-module-entry/check_seeded_run.py --upstream /path/to/pinned/rigorous
```

The independently authored fixtures exercise the empty control, both
seed placements, shadowing, caught and unmatched assertions, and
the two missing-exception diagnostics. Nested-call fixtures check
callee and argument error precedence, receipt order, assertion delivery,
and residual bindings. Unsupported fixtures run only in Lean. The
optional upstream check validates the revision and raw-file hashes
before emitting the same inputs under the empty, legacy and opt-in projections.
[Fixtures](../../tests/languages/python/source-module-entry/check_seeded_run.py)
