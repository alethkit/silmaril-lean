module

import Silmaril.SSA.SeaOfNodes.GCM.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM

private inductive Label : List Width → Type where
  | left : Label []
  | right : Label []
  | merge : Label [i1]

/-- The entry argument supplies the branch condition and the right-arm value.
The left arm has a binding before its jump. The merge returns its block argument. -/
private def cfg : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.condBr .here ⟨.left, .nil⟩ ⟨.right, .nil⟩)
  block
    | .left => .letOp (w := i1) () .nil (.terminator (.br ⟨.merge, .cons .here .nil⟩))
    | .right => .terminator (.br ⟨.merge, .cons .here .nil⟩)
    | .merge => .terminator (.ret (.cons .here .nil))

private def left : BlockId Label := some ⟨_, .left⟩
private def right : BlockId Label := some ⟨_, .right⟩
private def merge : BlockId Label := some ⟨_, .merge⟩

private def address : BlockId Label → List Nat
  | none => []
  | some ⟨_, .left⟩ => [0]
  | some ⟨_, .right⟩ => [1]
  | some ⟨_, .merge⟩ => [2]

private theorem address_injective {a b : BlockId Label} (eq : address a = address b) : a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [address] at eq
  · cases a <;> simp [address] at eq
  · cases a <;> cases b <;> simp_all [address]

private theorem entry_mem {b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) : none ∈ past := by
  induction path with
  | entry => simp
  | step _ _ _ ih => exact List.mem_cons_of_mem _ ih

private theorem endpoint_mem {b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) : b ∈ past := by
  cases path <;> exact List.mem_cons_self

private theorem left_path : EntryPath cfg left [left, none] := .step .entry .onTrue rfl

private theorem reachable (b : BlockId Label) : Reachable cfg b := by
  rcases b with _ | ⟨_, label⟩
  · exact ⟨[none], .entry⟩
  cases label
  · exact ⟨_, left_path⟩
  · exact ⟨[right, none], .step .entry .onFalse rfl⟩
  · exact ⟨[merge, left, none], .step left_path .jump rfl⟩

private theorem prefix_sound {a b : BlockId Label}
    (ancestry : List.IsPrefix (address a) (address b)) : Dominates cfg a b := by
  intro past path
  rcases a with _ | ⟨_, a⟩
  · exact entry_mem path
  have same : some ⟨_, a⟩ = b := by
    rcases b with _ | ⟨_, b⟩
    · cases a <;> simp [address] at ancestry
    · cases a <;> cases b <;> simp_all [address, List.cons_prefix_iff]
  rw [same]
  exact endpoint_mem path

private def tree : DominatorTree cfg where
  address := address
  entry_address := rfl
  address_injective := address_injective
  reachable := fun _ => true
  reachable_sound := fun {b} _ => reachable b
  prefix_sound := fun _ h => prefix_sound h

private def leftPhi : Use Label := .phi left .jump 0
private def leftEnd : Point Label := ⟨left, 1⟩
private def mergeStart : Point Label := ⟨merge, 0⟩

/-- The result can be inserted on the arm before its jump. The operand in
the request is available at that cut after the arm's existing binding. -/
theorem left_placement_legal : Legal cfg [leftEnd] [leftPhi] leftEnd :=
  checkPlacement_sound tree (by decide)

/-- Reading at the merge would accept insertion there. The same candidate
fails when the use is the incoming argument of the left jump. -/
theorem phi_destination_counterexample :
    checkPlacement tree [⟨none, 0⟩] [.ordinary mergeStart] mergeStart = true ∧
    checkPlacement tree [⟨none, 0⟩] [leftPhi] mergeStart = false := by
  decide

/-- Even with an arbitrary sound tree, the path to the left jump rules out
the merge as a valid definition site for this Phi use. -/
theorem phi_destination_illegal (operands : List (Point Label)) :
    ¬ Legal cfg operands [leftPhi] mergeStart := by
  intro legal
  obtain ⟨point, resolved, _, available⟩ := legal.uses_available leftPhi (by simp)
  have readAtLeft : leftPhi.point? cfg = some leftEnd := rfl
  rw [readAtLeft] at resolved
  cases resolved
  have visited := available.dominates _ left_path
  simp [mergeStart, merge, left] at visited

/-- Check branch occurrences, argument indices, and both sides of local order. -/
theorem rejects_invalid_sites :
    checkPlacement tree [] [.phi left .onTrue 0] leftEnd = false ∧
    checkPlacement tree [] [.phi left .jump 1] leftEnd = false ∧
    checkPlacement tree [leftEnd] [leftPhi] ⟨left, 0⟩ = false ∧
    checkPlacement tree [] [.ordinary ⟨left, 0⟩] leftEnd = false := by
  decide

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Regression
