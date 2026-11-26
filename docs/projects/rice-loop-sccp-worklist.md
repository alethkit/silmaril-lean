# Worklist scheduling for cyclic SCCP

`Loop.SCCP.Worklist.run` executes the existing typed carried-bank equations
as three FIFO jobs. Start queues control. At bottom the bank and result
equations already hold. [Simultaneous equations](rice-loop-sccp.md)

- Control watches the entry mark and, once entry is marked, the old bank.
- Φ watches the entry and backedge marks. It watches the old bank only
  when the backedge can contribute feedback.
- Result watches the exit mark and, once exit is marked, the old bank.

A pop evaluates one equation. It compares the three watched inputs after
the update and appends each affected job if it is absent from the queue.
Φ can re-enqueue itself when its new bank changes enabled feedback. The
job reads the whole feedback column from the old bank through the shared
abstract evaluator before replacing any field.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Defs.lean)

The queue potential is four times the remaining rank budget plus the
queue length. The invariant `state ≤ transfer state` makes every update
ascending. A strict ascent pays for up to three insertions. An unchanged
assignment triggers no insertion, so the pop decreases the potential
through queue length. `step_decreases` and `run_drains` certify the
budget, and `step_nodup` preserves duplicate suppression. The correctness
proof also keeps all equations absent from the queue satisfied and all
assignments below the simultaneous solution. When the queue empties,
`solve_eq_simultaneous` gives equality of the marks, every typed bank fact,
and the result fact. The native arrival and return coverage theorems
apply through this equality.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Thms.lean)

`report` shows the visited jobs, backedge and exit marks, and the latch
and result facts. The increment-one example first latches zero and then
widens when feedback contributes one. Equal feedback stops re-enqueuing
Φ. In the exit-only case, marking exit queues only result. The mixed-bank
example keeps the flag constant while the word widens. Its cross-field
test checks both a fresh Φ wakeup and suppression of an already pending
Φ, and the two new fields agree with the native feedback from the old bank.

```lean
module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Example

#eval latchAfter 3
#eval latchAfter 5
#eval report 0 .overdefined
#eval report 1 (.constant ⟨false⟩)
#eval bankReport
#eval crossFeedback []
#eval crossFeedback [.result, .phi]
```

This instantiates Cliff Click’s Rice dissertation §3.5 (printed p. 25)
for one pure Loop Region in the dual order. Jobs are the three equations
of this profile. The scheduler compares whole-bank views and evaluates
the shared acyclic header table when an active job needs it. Per-wire
scheduling, general CFGs, the dissertation’s complexity bound, and graph
rewrites are separate obligations.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Diamond scheduler](rice-diamond-sccp-worklist.md) ·
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Worklist/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
