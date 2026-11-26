# Folding a known branch in a typed diamond

`Diamond.SCCP.BranchFold.fold` reads the diamond’s predicate wire in the
simultaneous SCCP solution. A constant guard selects its If projection and
then its Region occurrence. The rewrite returns an existing `Pure.Program`
whose result is the Φ operand at that occurrence. The straight-line program
retains the shared producer table and contains no If, Region, or Φ.
[Typed SCCP](rice-diamond-sccp.md) · [Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/BranchFold/Defs.lean) ·
[Rice dissertation](https://hdl.handle.net/1911/16807)

`fold_eq_some_iff` specifies the returned program. `fold_eq_none_iff` says
that a bottom or overdefined guard is rejected. `executable_eq_singleton`
identifies the unique marked occurrence in the same fixed point.
`denote_eq` and `returns_iff` give native return correspondence at every
entry covered by the supplied facts. The proof uses coverage of the
predicate wire to select the same Region slot as native evaluation.
`lower_run_eq` gives the corresponding equality between the existing γ and
regionless RVSDG runs.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/BranchFold/Thms.lean)

The example’s true operand computes `x + x` and its false operand uses a
different producer, the literal 99. With a known true guard and an
unclassified `x`, the result fact is still overdefined. The emitted program
reads producer 1 and returns 8 or 24 for the two concrete inputs. The report
shows the result’s producer index, lowered region counts, and native value.

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Example.Defs

open Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Example

#eval originalRegions .onFalse                       -- [0, 0, 0, 0, 2]
#eval report .onFalse (.constant ⟨true⟩) true 4        -- some (some 1, [0, 0, 0], 8)
#eval report .onTrue (.constant ⟨true⟩) true 12        -- some (some 1, [0, 0, 0], 24)
#eval report .onTrue (.constant ⟨false⟩) false 4       -- some (some 2, [0, 0, 0], 99)
#eval report .onFalse .overdefined true 4             -- none
```

The guarantee is conditional on the entry facts and the pure primitive
model used for analysis. The producer table may retain unused pure producers.
Dead producer elimination, general CFG rewrites, and effectful control are
separate developments.
[Example graph](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/BranchFold/Example/Defs.lean) ·
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/SCCP/BranchFold/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
