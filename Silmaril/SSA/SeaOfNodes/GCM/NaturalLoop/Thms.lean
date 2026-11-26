module

public import Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.Correctness
import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms

/-! # Correctness of checked natural-loop placement -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}
variable {tree : DominatorTree cfg} {blocks : List (Target Label)} {edge : Backedge Label}

/-- The checked finite inventory covers precisely the structurally reachable blocks. -/
theorem mem_vertices_iff_reachable (checked : checkInventory tree blocks = true)
    (b : BlockId Label) : b ∈ vertices blocks ↔ Reachable cfg b :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.mem_vertices_iff_reachable checked b

/-- A checked descriptor supplies reachable endpoints, an actual successor
occurrence, and dominance of the latch by the header. -/
theorem checkBackedge_sound (checked : checkBackedge tree blocks edge = true) :
    Reachable cfg (some edge.header) ∧ Reachable cfg (some edge.latch) ∧
      (shape cfg (some edge.latch)).target edge.slot = some edge.header ∧
      Dominates cfg (some edge.header) (some edge.latch) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.checkBackedge_sound checked

/-- The output consists precisely of the header and reachable vertices that
can reach the latch in the CFG with the header omitted. -/
theorem checkedMembers_iff {loopMembers : List (BlockId Label)}
    (result : checkedMembers? tree blocks edge = some loopMembers)
    (b : BlockId Label) : b ∈ loopMembers ↔ Member cfg edge b :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.checkedMembers_iff result b

/-- The derived depth is one exactly for members of this natural loop. -/
theorem depth_eq_one_iff {loopMembers : List (BlockId Label)}
    (result : checkedMembers? tree blocks edge = some loopMembers)
    (b : BlockId Label) : depth tree loopMembers b = 1 ↔ Member cfg edge b :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.depth_eq_one_iff result b

/-- A selected cut has a validated descriptor and passes the actual CFG
operand and use constraints. -/
theorem choosePlacement_sound {operands : List (Point Label)} {uses : List (Use Label)}
    {chosen : Point Label} (found : choosePlacement tree blocks edge operands uses = some chosen) :
    checkBackedge tree blocks edge = true ∧ chosen ∈ candidateCuts cfg blocks ∧
      Legal cfg operands uses chosen :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.choosePlacement_sound found

/-- Among checker-admitted cuts, the selection minimizes the contribution
of this loop, then maximizes the supplied dominator address length. -/
theorem choosePlacement_minimal {loopMembers : List (BlockId Label)}
    (result : checkedMembers? tree blocks edge = some loopMembers)
    {operands : List (Point Label)} {uses : List (Use Label)} {chosen other : Point Label}
    (found : choosePlacement tree blocks edge operands uses = some chosen)
    (candidate : other ∈ candidateCuts cfg blocks)
    (checked : checkPlacement tree operands uses other = true) :
    depth tree loopMembers chosen.block ≤ depth tree loopMembers other.block ∧
      (depth tree loopMembers chosen.block = depth tree loopMembers other.block →
        (tree.address other.block).length ≤ (tree.address chosen.block).length) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.choosePlacement_minimal result found candidate checked

/-- After validating the descriptor, complete dominance and reachability
evidence makes an empty result equivalent to absence of a legal cut. -/
theorem choosePlacement_complete (valid : checkBackedge tree blocks edge = true)
    (complete : tree.Complete) (operands : List (Point Label)) (uses : List (Use Label)) :
    choosePlacement tree blocks edge operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, ¬ Legal cfg operands uses point :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.choosePlacement_complete valid complete operands uses

end Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop
