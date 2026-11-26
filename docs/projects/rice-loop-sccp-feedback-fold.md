# Folding a constant feedback operand

`Loop.SCCP.FeedbackFold.rewrite` takes a typed carried port and the literal
encoder from the return-fold API. It observes the selected operand in the
abstract backedge column at the original graph’s simultaneous solution.
The backedge must be marked, and the operand fact must be constant.
An unmarked backedge or a bottom operand gives `.unseen`. An overdefined
operand on a marked backedge gives `.overdefined`.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/FeedbackFold/Defs.lean) ·
[Return fold and literal encoder](rice-loop-sccp-return-fold.md)

The rewrite appends one native nullary producer and writes its origin into
one slot of the backedge column. Entry still supplies the original entry
column. The guard, return wire, and other feedback wires use their original
origins in the extended scope. Only the selected write is new.
[Typed graph construction and proof](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/FeedbackFold/Structure.lean)

`step_eq` applies at every activation reached by a covered input in the
original graph. The original SCCP arrival theorem covers the old latch.
The shared abstract evaluator then covers the concrete feedback column
read from that latch. Writing the inferred value into the selected slot
therefore preserves the whole next tuple. Induction on the backedge
budget gives `evalBackedges_eq`, and the native finite-return relation
gives `returns_iff` and `noFiniteReturn_iff`.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/FeedbackFold/Thms.lean)

In the example, entry provides zero and feedback computes one from the
captured start value. The joined latch becomes overdefined, while its
feedback operand remains constant. The fold redirects that operand to
the appended literal at producer 1. With a false flag there is a
return at budget zero. With a true flag the rewritten graph has no
finite return, and the regression proves that its observation is
`none` for every exact budget parameter. The changing or disabled
feedback cases use the existing increment-one counter.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/FeedbackFold/Regression.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Example

#eval feedbackProducer     -- Except.ok (some 1)
#eval run false 0           -- Except.ok (some 0)
#eval run true 12           -- Except.ok none
#eval refusal true          -- Except.error Refusal.overdefined
#eval refusal false         -- Except.error Refusal.unseen
```

The scope is one typed feedback operand in a total pure native loop.
The literal is certified in the analysis model, and the semantic
guarantees apply to inputs covered by the original analysis. The pass
retains the original producer table and uses the simultaneous solver.
Dead producer removal, general CFG rewriting, and scheduling changes
are separate.

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
