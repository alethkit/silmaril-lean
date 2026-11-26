module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.Correctness
import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms

/-! # Correctness of loop-aware placement choice -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

variable (tree : DominatorTree cfg) (loopDepth : BlockId Label → Nat) (blocks : List (Target Label))
variable (operands : List (Point Label)) (uses : List (Use Label))

/-- The chosen point is a represented cut with legal operand and use sites. -/
theorem chooseLoopPlacement_sound {chosen : Point Label}
    (found : chooseLoopPlacement tree loopDepth blocks operands uses = some chosen) :
    chosen ∈ candidateCuts cfg blocks ∧ Legal cfg operands uses chosen :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.chooseLoopPlacement_sound
    tree loopDepth blocks operands uses found

/-- Among checker-admitted cuts the supplied loop depth is minimal and, at
that depth, the supplied dominator address length is maximal. -/
theorem chooseLoopPlacement_minimal {chosen other : Point Label}
    (found : chooseLoopPlacement tree loopDepth blocks operands uses = some chosen)
    (member : other ∈ candidateCuts cfg blocks)
    (checked : checkPlacement tree operands uses other = true) :
    loopDepth chosen.block ≤ loopDepth other.block ∧
      (loopDepth chosen.block = loopDepth other.block →
        (tree.address other.block).length ≤ (tree.address chosen.block).length) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.chooseLoopPlacement_minimal
    tree loopDepth blocks operands uses found member checked

/-- Ranking and unranked discovery succeed on the same requests. -/
theorem chooseLoopPlacement_eq_none_iff :
    chooseLoopPlacement tree loopDepth blocks operands uses = none ↔
      discoverPlacement tree blocks operands uses = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.chooseLoopPlacement_eq_none_iff
    tree loopDepth blocks operands uses

/-- Under complete reachability and dominance evidence, failure excludes
every legal placement in the represented blocks. -/
theorem chooseLoopPlacement_complete (complete : tree.Complete) :
    chooseLoopPlacement tree loopDepth blocks operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, ¬ Legal cfg operands uses point :=
  (chooseLoopPlacement_eq_none_iff tree loopDepth blocks operands uses).trans
    (discoverPlacement_eq_none_iff_no_legal tree complete blocks operands uses)

end Silmaril.SSA.SeaOfNodes.GCM
