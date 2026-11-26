module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Correctness

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {blocks : List (Target Label)}
variable {proposed : BlockId Label → List Nat} {number : BlockId Label → Nat}
variable [DecidableEq (Target Label)]

/-- For a reachable target, accepted addresses reflect structural dominance
even when the proposed ancestor is unreachable or outside the inventory. -/
theorem prefix_iff_dominates (checked : check cfg blocks proposed = true)
    {a b : BlockId Label} (reachable : Reachable cfg b) :
    List.IsPrefix (address (reachableBlocks cfg blocks) number proposed a)
      (address (reachableBlocks cfg blocks) number proposed b) ↔ Dominates cfg a b :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.prefix_iff_dominates checked reachable

/-- Each reachable named block extends a reachable parent's address by one entry. -/
theorem parent_address (checked : check cfg blocks proposed = true)
    {b : Target Label} (reachable : Reachable cfg (some b)) :
    ∃ parent childIndex, Reachable cfg parent ∧
      address (reachableBlocks cfg blocks) number proposed (some b) =
        address (reachableBlocks cfg blocks) number proposed parent ++ [childIndex] :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.parent_address checked reachable

/-- Every reachable named block has a strict dominator dominated by all of its
strict dominators. This is the parent identified by the one-step address. -/
theorem immediate_dominator (checked : check cfg blocks proposed = true)
    (injective : Function.Injective number) {b : Target Label}
    (reachable : Reachable cfg (some b)) :
    ∃ parent, Reachable cfg parent ∧ parent ≠ some b ∧ Dominates cfg parent (some b) ∧
      ∀ a, a ≠ some b → Dominates cfg a (some b) → Dominates cfg a parent :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.immediate_dominator checked injective reachable

/-- Validate a proposal and supply complete evidence to the existing placement
APIs. Injective label numbers supply disjoint addresses for unreachable blocks. -/
def certify? (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (proposed : BlockId Label → List Nat) (number : BlockId Label → Nat)
    (injective : Function.Injective number) :
    Option {tree : DominatorTree cfg // tree.Complete} :=
  if checked : check cfg blocks proposed = true then
    have closed : checkClosed cfg blocks = true := by
      exact Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.check_closed checked
    have member (b : BlockId Label) : b ∈ reachableBlocks cfg blocks ↔ Reachable cfg b := by
      exact Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.mem_reachableBlocks_iff closed b
    some ⟨{
      address := address (reachableBlocks cfg blocks) number proposed
      entry_address := by exact Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.entry_address checked
      address_injective := fun {_ _} same => by
        exact Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.address_injective checked injective same
      reachable := fun b => decide (b ∈ reachableBlocks cfg blocks)
      reachable_sound := fun {b} hit => (member b).mp (of_decide_eq_true hit)
      prefix_sound := fun reachable => (prefix_iff_dominates checked reachable).mp
    }, {
      reachable_complete := fun {b} reachable => decide_eq_true ((member b).mpr reachable)
      prefix_complete := fun reachable => (prefix_iff_dominates checked reachable).mpr
    }⟩
  else none

end Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree
