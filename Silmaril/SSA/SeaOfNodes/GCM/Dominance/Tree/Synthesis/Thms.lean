module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {blocks : List (Target Label)}
variable {a b : BlockId Label}
variable [DecidableEq (Target Label)]

/-- A reachable named block has a computed parent that is dominated by all
of its strict dominators. -/
theorem immediateParent?_spec (closed : checkClosed cfg blocks = true)
    (reachable : Reachable cfg b) (named : b ≠ none) :
    ∃ parent, immediateParent? cfg blocks b = some parent ∧ Reachable cfg parent ∧
      parent ≠ b ∧ Dominates cfg parent b ∧
      ∀ a, a ≠ b → Dominates cfg a b → Dominates cfg a parent :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.immediateParent?_spec closed reachable named

/-- The inventory length suffices to trace every reachable block to entry. -/
theorem traceAddress?_some (closed : checkClosed cfg blocks = true) (reachable : Reachable cfg b) :
    ∃ path, traceAddress? cfg blocks (reachableBlocks cfg blocks).length b = some path :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.traceAddress?_some closed reachable

/-- Synthesized address prefixes are exact for reachable pairs. -/
theorem proposedAddress_prefix_iff (closed : checkClosed cfg blocks = true)
    (ra : Reachable cfg a) (rb : Reachable cfg b) :
    List.IsPrefix (proposedAddress cfg blocks a) (proposedAddress cfg blocks b) ↔
      Dominates cfg a b :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.proposedAddress_prefix_iff closed ra rb

/-- The synthesized proposal passes all checks on a successor-closed inventory. -/
theorem check_proposedAddress (closed : checkClosed cfg blocks = true) :
    Tree.check cfg blocks (proposedAddress cfg blocks) = true :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.check_proposedAddress closed

/-- With the numbering required by the existing tree API, synthesis returns
a certified complete tree exactly when the inventory is successor-closed. -/
theorem synthesize?_isSome_iff (number : BlockId Label → Nat) (injective : Function.Injective number) :
    (synthesize? cfg blocks number injective).isSome = true ↔ checkClosed cfg blocks = true :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.synthesize?_isSome_iff number injective

end Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis
