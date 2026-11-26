# Sparse scheduling for diamond SCCP

`Diamond.SCCP.Worklist.run` uses a FIFO queue for the three equations of
the native typed diamond. The initial queue contains branch and producers.
An empty executable set already gives Φ its initial bottom value.
[Rice dissertation §3.5](https://hdl.handle.net/1911/16807) ·
[Simultaneous equations](rice-diamond-sccp.md) ·
[Worklist definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/Worklist/Defs.lean)

The producers job computes the unconditional ranked slice once from the
entry facts, using the same evaluation and lookup functions as
`SCCP.producerFacts`. It shares the resulting typed table across reads.
A changed predicate fact queues branch. A changed fact at a
marked Φ operand queues Φ. The branch job queues Φ when the executable set
changes, and Φ has no consumers in this profile. A job already in the queue
keeps its position. An empty queue ends the run immediately.

The potential adds weights 4, 2, and 1 for producers, branch, and Φ.
A popped job costs more than all of the jobs it can append. The initial
budget of six therefore suffices even if multiple jobs observe changes.
`step_decreases` proves the strict decrease and `run_drains` proves that
nothing remains pending after the run. The correctness invariant says that
each equation absent from the queue already holds. A second invariant uses
monotonicity to keep every intermediate assignment below the simultaneous
least fixed point. When the queue drains, all equations hold. Leastness then
gives `solve_eq_simultaneous`, an equality of the full typed fact assignments.
The simultaneous solver's soundness theorems apply through this equality.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/Worklist/Thms.lean)

The example has a producer for the predicate and Region order false, then
true. Each report shows visited jobs, the two Region flags, and the returned
Φ fact. With a known true guard the result is constant 14 and only the
second slot is marked. With an overdefined guard both slots are marked and
the result is overdefined. Both runs revisit branch once after the predicate
fact arrives. With no predicate evidence the trace stops after the first
two jobs.

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Example.Defs

open Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Example

#eval report (.constant ⟨true⟩)
#eval report .overdefined
#eval report .bottom
#eval pendingAfterLearning 3  -- []     false operand at an unmarked occurrence
#eval pendingAfterLearning 2  -- [.phi] true operand at the marked occurrence
#eval pendingAfterLearning 0  -- [.branch] predicate producer
```

The producer slice uses its existing dependency order. The worklist
schedules the three diamond equations at their defined granularity.
General CFGs, cyclic producer scheduling, scheduling cost in a general
graph, and graph rewrites are separate developments.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/SCCP/Worklist/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
