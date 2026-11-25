module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PartialDefs
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Ports

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing (left_ne_right)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

theorem lowerPart_fromLower (w : Fin A) :
    lowerPart (fromLower (lower := lower) (upper := upper) w) = some w := by
  simp only [fromLower]
  split <;> rfl

theorem upperPart_fromUpper (w : Fin B) : m.upperPart (m.fromUpper w) = some w := by
  simp only [fromUpper]
  split
  · simp [upperPart]
  · rfl

theorem lower_exists {z : WireId lower upper} {w : Fin A} :
    fromLower w = z ↔ lowerPart z = some w := by
  refine ⟨fun h => h ▸ lowerPart_fromLower w, ?_⟩
  intro h
  rcases z with z | (z | z)
  · have eq : z.val = w := Option.some.inj h
    subst w
    simp [fromLower, z.property]
  · have eq : z.val = w := Option.some.inj h
    subst w
    simp [fromLower, z.property]
  · cases h

theorem upper_exists {z : WireId lower upper} {w : Fin B} :
    m.fromUpper w = z ↔ m.upperPart z = some w := by
  refine ⟨fun h => h ▸ upperPart_fromUpper m w, ?_⟩
  intro h
  rcases z with z | (z | z)
  · cases h
  · have eq : (m.contact z).val = w := Option.some.inj h
    subst w
    have hm := (m.contact z).property
    have hs : (⟨(m.contact z).val, hm⟩ : {w : Fin B // upper.start w = none}) = m.contact z :=
      Subtype.ext rfl
    simp only [fromUpper, dite_eq_left hm, hs, Equiv.symm_apply_apply]
  · have eq : z.val = w := Option.some.inj h
    subst w
    simp [fromUpper, z.property]

theorem fromLower_injective : Function.Injective (fromLower (lower := lower) (upper := upper)) := by
  intro w z h
  exact Option.some.inj (((lower_exists).mp h).symm.trans (lowerPart_fromLower z))

theorem fromUpper_injective : Function.Injective m.fromUpper := by
  intro w z h
  exact Option.some.inj (((upper_exists m).mp h).symm.trans (upperPart_fromUpper m z))

theorem fromLower_shared (w : Contact lower) :
    fromLower (upper := upper) w.val = .inr (.inl w) :=
  lower_exists.mpr rfl

theorem fromUpper_shared (w : Contact lower) :
    m.fromUpper (m.contact w).val = .inr (.inl w) :=
  (upper_exists m).mpr rfl

theorem fromLower_eq_fromUpper {a : Fin A} {b : Fin B} :
    fromLower a = m.fromUpper b ↔ ∃ w : Contact lower, w.val = a ∧ (m.contact w).val = b := by
  constructor
  · intro eq
    generalize hz : fromLower a = z at eq
    have left := lower_exists.mp hz
    have right := (upper_exists m).mp eq.symm
    rcases z with z | (z | z)
    · cases right
    · exact ⟨z, Option.some.inj left, Option.some.inj right⟩
    · cases left
  · rintro ⟨w, rfl, rfl⟩
    exact (fromLower_shared w).trans (fromUpper_shared m w).symm

def wireStart : WireId lower upper → Option (Fin (L + R)) :=
  Sum.elim (fun w => (lower.start w.val).map (Fin.castAdd R))
    (Sum.elim (fun w => (lower.start w.val).map (Fin.castAdd R))
      (fun w => (upper.start w.val).map (Fin.natAdd L)))

def wireFinish : WireId lower upper → Option (Fin (L + R)) :=
  Sum.elim (fun w => (lower.finish w.val).map (Fin.castAdd R))
    (Sum.elim (fun w => (upper.finish (m.contact w).val).map (Fin.natAdd L))
      (fun w => (upper.finish w.val).map (Fin.natAdd L)))

def wireLabel : WireId lower upper → O :=
  Sum.elim (fun w => lower.label w.val)
    (Sum.elim (fun w => lower.label w.val) (fun w => upper.label w.val))

theorem label_fromLower (w : Fin A) : wireLabel (fromLower (lower := lower) (upper := upper) w) = lower.label w := by
  unfold fromLower
  split <;> rfl

theorem label_fromUpper (w : Fin B) : wireLabel (m.fromUpper w) = upper.label w := by
  unfold fromUpper
  split
  · next hs =>
    change lower.label (m.contact.symm ⟨w, hs⟩).val = upper.label w
    simpa only [Equiv.apply_symm_apply] using m.label (m.contact.symm ⟨w, hs⟩)
  · rfl

private theorem right_ne_left (j : Fin R) (v : Fin L) :
    Fin.natAdd L j ≠ Fin.castAdd R v :=
  (left_ne_right v j).symm

theorem start_left_iff (z : WireId lower upper) (v : Fin L) :
    wireStart z = some (Fin.castAdd R v) ↔
      ∃ w, fromLower w = z ∧ lower.start w = some v := by
  simp only [lower_exists]
  rcases z with z | (z | z)
  · simp [wireStart, lowerPart]
  · simp [wireStart, lowerPart]
  · simp [wireStart, lowerPart, right_ne_left]

theorem finish_left_iff (z : WireId lower upper) (v : Fin L) :
    wireFinish m z = some (Fin.castAdd R v) ↔
      ∃ w, fromLower w = z ∧ lower.finish w = some v := by
  simp only [lower_exists]
  rcases z with z | (z | z)
  · simp [wireFinish, lowerPart]
  · simp [wireFinish, lowerPart, right_ne_left, z.property]
  · simp [wireFinish, lowerPart, right_ne_left]

theorem start_right_iff (z : WireId lower upper) (v : Fin R) :
    wireStart z = some (Fin.natAdd L v) ↔
      ∃ w, m.fromUpper w = z ∧ upper.start w = some v := by
  simp only [upper_exists m]
  rcases z with z | (z | z)
  · simp [wireStart, upperPart, left_ne_right]
  · simp [wireStart, upperPart, left_ne_right, (m.contact z).property]
  · simp [wireStart, upperPart]

theorem finish_right_iff (z : WireId lower upper) (v : Fin R) :
    wireFinish m z = some (Fin.natAdd L v) ↔
      ∃ w, m.fromUpper w = z ∧ upper.finish w = some v := by
  simp only [upper_exists m]
  rcases z with z | (z | z)
  · simp [wireFinish, upperPart, left_ne_right]
  · simp [wireFinish, upperPart]
  · simp [wireFinish, upperPart]

theorem start_on_cap {z : WireId lower upper} (h : wireStart z = none) :
    ∃ w, fromLower w = z ∧ lower.start w = none := by
  simp only [lower_exists]
  rcases z with z | (z | z)
  · exact ⟨_, rfl, by simpa [wireStart] using h⟩
  · exact ⟨_, rfl, by simpa [wireStart] using h⟩
  · exact (z.property (by simpa [wireStart] using h)).elim

theorem finish_on_cap {z : WireId lower upper} (h : wireFinish m z = none) :
    ∃ w, m.fromUpper w = z ∧ upper.finish w = none := by
  simp only [upper_exists m]
  rcases z with z | (z | z)
  · exact (z.property (by simpa [wireFinish] using h)).elim
  · exact ⟨_, rfl, by simpa [wireFinish] using h⟩
  · exact ⟨_, rfl, by simpa [wireFinish] using h⟩

end Silmaril.RuntimeWires.Proofs.PartialGluing
