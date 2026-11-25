module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Pieces
import Mathlib.Tactic.Tauto

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.Whiskering

open ProgressiveGraph CollarAssociator
open HorizontalPlacement (placed slots active_slot_x idle_slot_x)
open CapClasses (matching glue)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c : FixedCap S}
variable (s : ActiveStrip) (idle : FixedCap S)
variable (p : FixedDrawing S a.profile b.profile) (q : FixedDrawing S b.profile c.profile)

local notation "I" => idle.profile.size
local notation "m" => matching p q
local notation "n" => wideMatch s idle p q
local notation "P" => stackThenPlace s idle p q
local notation "Q" => placeThenStack s idle p q
abbrev stackedCount := (glue p q).wires

abbrev collarName (i : Fin b.profile.size) :=
  Fin.castAdd I (leftWire m (p.output i).val)

local notation "leftName" => Fin.castAdd I ∘ leftWire m
local notation "rightName" => Fin.castAdd I ∘ rightWire m
local notation "idleName" => Fin.natAdd (stackedCount p q)
local notation "centreName" => collarName idle p q
local notation "centreX" => fun i => s.place (b.profile.x i)

def pieces (w : Fin ((glue p q).wires + I)) (z : ℝ × ℝ) : Prop :=
  placedPiece s p.drawing leftName Height.lower w z ∨
    verticalPiece centreName Height.collar centreX w z ∨
    placedPiece s q.drawing rightName Height.upper w z ∨
    idlePiece s idle idleName id w z

theorem stack_place_trace (w : Fin ((glue p q).wires + I)) (z : ℝ × ℝ) :
    z ∈ ((P).drawing.wire w).trace ↔ pieces s idle p q w z := by
  refine (trace_mem (HorizontalPlacement.drawing s (glue p q).drawing idle) w z).trans ?_
  refine (piece_placed s (glue p q).drawing idle id id w z).trans ?_
  refine (or_congr (placed_active_pieces s p q (Fin.castAdd I) w z) Iff.rfl).trans ?_
  unfold pieces
  tauto

theorem wide_lower_piece (w : Fin ((glue p q).wires + I)) (z : ℝ × ℝ) :
    wirePiece (placed s idle p).drawing (back s idle p q ∘ leftWire n) Height.lower w z ↔
      placedPiece s p.drawing leftName Height.lower w z ∨
      idlePiece s idle idleName Height.lower w z := by
  refine (piece_placed s p.drawing idle (back s idle p q ∘ leftWire n) Height.lower w z).trans ?_
  have la : (back s idle p q ∘ leftWire n) ∘ Fin.castAdd I = leftName := by
    funext i
    change back s idle p q (leftWire n (Fin.castAdd I i)) = _
    rw [back_lower, toLower, Fin.append_left]
  have li : (back s idle p q ∘ leftWire n) ∘ Fin.natAdd p.wires = idleName := by
    funext i
    change back s idle p q (leftWire n (Fin.natAdd p.wires i)) = _
    rw [back_lower, toLower, Fin.append_right]
  exact or_congr
    (Iff.of_eq (congrArg (fun name => placedPiece s p.drawing name Height.lower w z) la))
    (Iff.of_eq (congrArg (fun name => idlePiece s idle name Height.lower w z) li))

theorem wide_upper_piece (w : Fin ((glue p q).wires + I)) (z : ℝ × ℝ) :
    wirePiece (placed s idle q).drawing (back s idle p q ∘ rightWire n) Height.upper w z ↔
      placedPiece s q.drawing rightName Height.upper w z ∨
      idlePiece s idle idleName Height.upper w z := by
  refine (piece_placed s q.drawing idle (back s idle p q ∘ rightWire n) Height.upper w z).trans ?_
  have ra : (back s idle p q ∘ rightWire n) ∘ Fin.castAdd I = rightName := by
    funext i
    change back s idle p q (rightWire n (Fin.castAdd I i)) = _
    rw [back_upper, toUpper, Fin.append_left]
  have ri : (back s idle p q ∘ rightWire n) ∘ Fin.natAdd q.wires = idleName := by
    funext i
    change back s idle p q (rightWire n (Fin.natAdd q.wires i)) = _
    rw [back_upper, toUpper, Fin.append_right]
  exact or_congr
    (Iff.of_eq (congrArg (fun name => placedPiece s q.drawing name Height.upper w z) ra))
    (Iff.of_eq (congrArg (fun name => idlePiece s idle name Height.upper w z) ri))

theorem wide_collar_piece (w : Fin ((glue p q).wires + I)) (z : ℝ × ℝ) :
    collarPiece n (fun k => back s idle p q (leftWire n k.val)) Height.collar w z ↔
      verticalPiece centreName Height.collar centreX w z ∨
      idlePiece s idle idleName Height.collar w z := by
  rw [collar_slots]
  have active (i : Fin b.profile.size) :
      back s idle p q (leftWire n ((placed s idle p).output ((slots s b idle).symm (.inl i))).val) =
        (centreName) i := by
    rw [output_active, back_lower, toLower, Fin.append_left]
    rfl
  have added (i : Fin I) :
      back s idle p q (leftWire n ((placed s idle p).output ((slots s b idle).symm (.inr i))).val) =
        idleName i := by
    rw [output_idle, back_lower, toLower, Fin.append_right]
  constructor
  · rintro ⟨k, y, id, hy, point⟩
    obtain ⟨slot, rfl⟩ := (slots s b idle).symm.surjective k
    cases slot with
    | inl i =>
      exact .inl ⟨i, y, (active i).symm.trans id, hy,
        (congrArg (fun x : ℝ => (x, Height.collar y)) (active_slot_x s b idle i)).symm.trans point⟩
    | inr i =>
      exact .inr ⟨i, y, (added i).symm.trans id, hy,
        (congrArg (fun x : ℝ => (x, Height.collar y)) (idle_slot_x s b idle i)).symm.trans point⟩
  · rintro (⟨i, y, id, hy, point⟩ | ⟨i, y, id, hy, point⟩)
    · exact ⟨(slots s b idle).symm (.inl i), y, (active i).trans id, hy,
        (congrArg (fun x : ℝ => (x, Height.collar y)) (active_slot_x s b idle i)).trans point⟩
    · exact ⟨(slots s b idle).symm (.inr i), y, (added i).trans id, hy,
        (congrArg (fun x : ℝ => (x, Height.collar y)) (idle_slot_x s b idle i)).trans point⟩

theorem reindex_trace {L A : ℕ} (d : ProgressiveGraph.Diagram S L A .point)
    {N : ℕ} (rename : Fin N ≃ Fin A) (w : Fin N) (z : ℝ × ℝ) :
    z ∈ (d.wire (rename w)).trace ↔ wirePiece d rename.symm id w z := by
  constructor
  · rintro ⟨y, cover, rfl⟩
    exact ⟨rename w, y, rename.symm_apply_apply w, cover, rfl⟩
  · rintro ⟨i, y, eq, cover, point⟩
    have hi : i = rename w := (rename.apply_symm_apply i).symm.trans (congrArg rename eq)
    subst i
    exact ⟨y, cover, point⟩

theorem place_stack_trace (w : Fin ((glue p q).wires + I)) (z : ℝ × ℝ) :
    z ∈ ((Q).drawing.wire (wireEquiv s idle p q w)).trace ↔ pieces s idle p q w z := by
  refine (reindex_trace (n).glue (wireEquiv s idle p q) w z).trans ?_
  refine (collared_expand n (back s idle p q) id w z).trans ?_
  refine (or_congr (wide_lower_piece s idle p q w z)
    (or_congr (wide_collar_piece s idle p q w z) (wide_upper_piece s idle p q w z))).trans ?_
  unfold pieces
  have idleTrace := idle_interval_union idleName (fun i : Fin I => s.opposite.place (idle.profile.x i)) w z
  tauto

end Silmaril.RuntimeWires.Proofs.Whiskering
