# Finite correspondence for the Python closure executor

The [store and dispatch projection](python-closure-finite-projection.md)
relates finite storage operations, checked code lookup, positional
binding and saved-caller delivery to their Core counterparts. The
executor projection assembles these equations at the actual
[Core step boundary](../../Silmaril/Languages/Python/Core/Closure/Executor/Thms.lean).
The fixed code table is the view of finite rows. Machine states retain
the original typed frames, bodies, continuations, stacks and result
payloads. Each state carries a finite heap, with its exact frontier and
cell addresses. Both sides use the same ambient global lookup.

`advanceIn_project` preserves the optional label and the full projected
successor for every executor state. `stepIn_iff` relates the finite
selector to the Core inductive step relation from a specified finite
source. `executionIn_readback` threads the recovered witness through the
whole finite run. It preserves every action, including silent actions,
and every projected state. `runPrefixIn_project` relates the executors'
fuel-bounded prefixes, visible event lists and residual states for a
fixed lookup. The original interfaces use the empty lookup.

The same correspondence covers failed code lookup, defined exceptions,
return delivery and successful result storage in the caller. Finished
states expose their existing `Result` and faults remain in the
machine's fault state and event. The fixtures exercise a callee write
that persists through success and exception propagation, exact saved
frame restoration and a missing-code fault.
[Projection theorems](../../Silmaril/Languages/Python/Core/Closure/Finite/Executor/Thms.lean)
· [Fixtures](../../Silmaril/Languages/Python/Core/Closure/Finite/Executor/Examples.lean)

The scope is the fixed positional closure executor. Its code-table
and initial heap hypotheses are the existence of the finite witnesses
described by the store and dispatch projection. A fuel-bounded prefix
can end in a live state. Full source-level linking and a serialized
symbolic-state codec have separate correspondence obligations.

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Core.Closure.Finite.Executor.Examples +Silmaril.Languages.Python.Core.Locals.Finite.Examples'
```
