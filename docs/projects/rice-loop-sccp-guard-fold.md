# Specializing a native loop guard

`Loop.SCCP.GuardFold.rewrite` reads the guard fact over the final bank
of the original loop. A constant emits a native `Loop.Graph` whose
predicate wire reads a new certified Boolean literal. The preheader,
entry column, feedback operands, and returned value retain their
original wires in the corresponding scopes. The fixed native loop
shape retains its two successor slots. The new predicate specializes
the choice to one of them.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/GuardFold/Defs.lean) ·
[Loop SCCP](rice-loop-sccp.md)

`executable_eq` gives the fixed-point occurrence set from the guard.
False permits exit, true permits feedback, bottom contributes neither
tail successor, and overdefined contributes both. `rewrite_error_iff`
identifies the unseen and overdefined refusals. An early constant that
widens across activations therefore gives no rewrite.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/GuardFold/Thms.lean)

The proof reads the original guard from each reached latch. The
original SCCP arrival and producer coverage theorems make this value
equal to the literal. `step_eq` therefore preserves both the successor
choice and its entire payload. The shared lockstep theorem gives
`evalBackedges_eq` at every budget from Start. `returns_iff` and
`noFiniteReturn_iff` follow from the native finite-return relation.

The fixture uses an external flag. False returns at budget zero. True
takes feedback and diverges, with `none` proved at every budget after
specialization. An unseen flag leaves just entry marked and refuses.
An unclassified flag and the counter whose guard changes across
iterations also refuse.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/GuardFold/Regression.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Example

#eval predicateProducer (.constant ⟨false⟩)  -- Except.ok (some 1)
#eval run false 0                            -- Except.ok (some 0)
#eval run true 12                            -- Except.ok none
#eval predicateProducer .bottom             -- Except.error Refusal.unseen
#eval predicateProducer .overdefined        -- Except.error Refusal.overdefined
#eval varyingGuard                           -- Except.error Refusal.overdefined
```

Rice §3.6 Figure 3.7 (printed p. 26) gives the loop reachability equations
for the two exits of the tail test. §3.7 Figure 3.8 (p. 28) connects a
constant test to reachability, and §3.8.1 (pp. 33–34) uses the solved
facts in transformation. The pinned scan has SHA-256
`30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
This slice covers one typed pure native loop under covered inputs.
Physical edge removal, dead producers, and general CFG rewriting are
separate developments.
[Rice inventory](sea-of-nodes.md#rice-dissertation) ·
[Pinned scan](https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content) ·
[Diamond branch fold](rice-diamond-sccp-branch-fold.md)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
