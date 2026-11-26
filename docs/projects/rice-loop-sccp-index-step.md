# Locate SCCP notifications from the popped job

`Split.Index.runSteps` uses `Index.stepLocal`. A Φ pop publishes exactly
one typed destination, so with feedback enabled and the marks unchanged,
the step compares that destination alone and reads its reverse-index bucket
if the fact changed. A control pop writes edge marks. A result pop writes
the result fact. Neither writes the carried bank. A change to the entry or
feedback mark still wakes all Φ destinations.
[Implementation](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Defs.lean)

Both steps share the queue insertion and the original entry-gated control
and exit-gated result watches. These watches can still compare entire banks.
`Index.wake` accepts arbitrary assignment pairs, and `Index.step` is the
reference step that uses it. `Index.stepLocal_eq` checks equality of the
whole assignment and pending queue, and `Index.runSteps_eq_step` checks
every budget including the visit trace. The existing solver theorems still
prove that the queue drains and the full assignment equals the simultaneous
solution. [Theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Thms.lean)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step.Example

#eval noOp
-- (true, (constant true, constant 255), [result], [phi 1])

#eval transitiveWake
-- (true, (constant true, constant 255), [control, phi 0, phi 1], [phi 1])

#eval feedbackActivation
-- (true, (constant true, constant 255), [phi 1, phi 0], [control])
```

Each report gives the feedback mark, Boolean and byte facts, pending queue,
and visits. The Boolean feedback reads the byte through two producers.
Publishing the byte from bottom wakes both its transitive reader and its
direct self-reader. Activating feedback appends the Boolean job behind the
already pending byte job.
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Step/Regression.lean)

Click's *Combining Analyses, Combining Optimizations*, §3.5 (printed p. 25),
requeues users of a changed variable. This step uses the known destination
of a single equation pop in the current pure single-loop profile.
[Reverse index](rice-loop-sccp-index.md) · [Rice dissertation](https://hdl.handle.net/1911/16807)
