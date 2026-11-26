module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Dominance

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {blocks : List (Target Label)}

/-- The projection preserves the source slot and its typed target. -/
theorem mem_occurrences_iff {src : BlockId Label} {slot : EdgeSlot} {dst : Target Label} :
    (slot, dst) ∈ occurrences cfg src ↔ (shape cfg src).target slot = some dst :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.mem_occurrences_iff

/-- The initial candidate count is sufficient fuel for closure, even when
the inventory contains duplicates. -/
theorem boundedClose_eq_reverseClose {B : Type} [DecidableEq B] (edge : B → B → Bool)
    (fuel : Nat) (remaining reached : List B) (bound : remaining.length ≤ fuel) :
    boundedClose edge fuel remaining reached =
      NaturalLoop.reverseClose edge remaining reached :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.boundedClose_eq_reverseClose edge fuel remaining reached bound

variable [DecidableEq (Target Label)]

/-- Successor closure covers every structural path from entry. -/
theorem path_endpoint_mem (checked : checkClosed cfg blocks = true)
    {b : BlockId Label} {past : List (BlockId Label)} (path : EntryPath cfg b past) :
    b ∈ NaturalLoop.vertices blocks :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.path_endpoint_mem checked path

/-- The bounded traversal computes exactly the paths whose vertices are kept. -/
theorem reachesKeeping?_iff (checked : checkClosed cfg blocks = true)
    (keep : BlockId Label → Bool) (b : BlockId Label) :
    reachesKeeping? cfg blocks keep b = true ↔
      ∃ past, EntryPath cfg b past ∧ ∀ v ∈ past, keep v = true :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.reachesKeeping?_iff checked keep b

/-- On a closed inventory, executable reachability agrees with structural reachability. -/
theorem reachable?_iff (checked : checkClosed cfg blocks = true) (b : BlockId Label) :
    reachable? cfg blocks b = true ↔ Reachable cfg b :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.reachable?_iff checked b

/-- A successful query characterizes structural dominance of a reachable target. -/
theorem dominates?_iff (a b : BlockId Label) :
    dominates? cfg blocks a b = true ↔
      checkClosed cfg blocks = true ∧ Reachable cfg b ∧ Dominates cfg a b :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.dominates?_iff a b

end Silmaril.SSA.SeaOfNodes.GCM.Dominance
