module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Contacts
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialIndexes

public section

namespace Silmaril.RuntimeWires.Proofs.CollarAssociator

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch
open ProgressiveGraph.Diagram.OrderedVerticalMatch (collarIndex collarCount)
open PartialGluing (lower_exists upper_exists)

universe u v w
variable {O : Type u} {S : Signature.{u,v} O} {L M A B : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}

theorem partial_cases (j : d.PartialVerticalMatch e) (z : Fin (wireCount d e)) :
    (∃ a, lowerId (upper := e) a = z) ∨ ∃ b, j.upperId b = z := by
  let n := numbering d e
  have lo {t : WireId d e} {a : Fin A} (h : fromLower a = t) (eq : n.symm z = t) :
      lowerId (upper := e) a = z := (congrArg n (h.trans eq.symm)).trans (n.apply_symm_apply z)
  rcases eq : n.symm z with a | (a | b)
  · exact .inl ⟨a.val, lo (lower_exists.mpr rfl) eq⟩
  · exact .inl ⟨a.val, lo (lower_exists.mpr rfl) eq⟩
  · have id : j.fromUpper b.val = .inr (.inr b) := (upper_exists j).mpr rfl
    exact .inr ⟨b.val, (congrArg n (id.trans eq.symm)).trans (n.apply_symm_apply z)⟩

variable (m : d.OrderedVerticalMatch e)

theorem collar_from_lower (i : Fin (collarCount d)) :
    m.lowerJoin.upperId i = lowerId (upper := m.collar) ((collarIndex d).symm i).val := by
  symm
  apply m.lowerJoin.lowerId_eq_upperId.mpr
  refine ⟨(collarIndex d).symm i, rfl, ?_⟩
  change collarIndex d ((collarIndex d).symm i) = i
  exact (collarIndex d).apply_symm_apply i

theorem wire_cases (z : Fin (wireCount m.lowerJoin.glue e)) :
    (∃ a, leftWire m a = z) ∨ ∃ b, rightWire m b = z := by
  rcases partial_cases m.upperJoin z with ⟨x, id⟩ | ⟨b, id⟩
  · rcases partial_cases m.lowerJoin x with ⟨a, ha⟩ | ⟨i, hi⟩
    · exact .inl ⟨a, by unfold leftWire; rw [ha, id]⟩
    · exact .inl ⟨((collarIndex d).symm i).val, by
        unfold leftWire
        rw [← collar_from_lower m i, hi, id]⟩
  · exact .inr ⟨b, id⟩

theorem left_injective : Function.Injective (leftWire m) :=
  (lowerId_injective (lower := m.lowerJoin.glue) (upper := e)).comp
    (lowerId_injective (lower := d) (upper := m.collar))

theorem right_injective : Function.Injective (rightWire m) := m.upperJoin.upperId_injective

theorem wire_contact (a : Contact d) :
    leftWire m a.val = rightWire m (m.contact a).val := m.glue_matches_contact a

theorem wire_overlap {a : Fin A} {b : Fin B} (h : leftWire m a = rightWire m b) :
    ∃ x : Contact d, x.val = a ∧ (m.contact x).val = b := by
  obtain ⟨z, za, _⟩ := m.upperJoin.lowerId_eq_upperId.mp h
  obtain ⟨i, _, eq⟩ := m.lowerJoin.glue_output_cap_exists z.property
  have aEq : ((collarIndex d).symm i).val = a :=
    (lowerId_injective (lower := d) (upper := m.collar))
      ((collar_from_lower m i).symm.trans (eq.trans za))
  refine ⟨(collarIndex d).symm i, aEq, right_injective m ?_⟩
  exact (wire_contact m ((collarIndex d).symm i)).symm.trans ((congrArg (leftWire m) aEq).trans h)

variable {T : Type w}

/-- Eliminate a composite wire by choosing an operand representative.
The supplied equation makes the choice unambiguous at the splice. -/
noncomputable def descend (l : Fin A → T) (r : Fin B → T) (z : Fin (wireCount m.lowerJoin.glue e)) : T :=
  if h : ∃ a, leftWire m a = z then l (Classical.choose h)
  else r (Classical.choose ((wire_cases m z).resolve_left h))

theorem descend_left (l : Fin A → T) (r : Fin B → T) (a : Fin A) :
    descend m l r (leftWire m a) = l a := by
  let h : ∃ a', leftWire m a' = leftWire m a := ⟨a, rfl⟩
  unfold descend
  rw [dite_eq_left h]
  exact congrArg l (left_injective m (Classical.choose_spec h))

theorem descend_right (l : Fin A → T) (r : Fin B → T)
    (agree : ∀ a : Contact d, l a.val = r (m.contact a).val) (b : Fin B) :
    descend m l r (rightWire m b) = r b := by
  unfold descend
  split
  · next h =>
    obtain ⟨x, xa, xb⟩ := wire_overlap m (Classical.choose_spec h)
    exact (congrArg l xa.symm).trans ((agree x).trans (congrArg r xb))
  · next h =>
    exact congrArg r (right_injective m (Classical.choose_spec ((wire_cases m _).resolve_left h)))

end Silmaril.RuntimeWires.Proofs.CollarAssociator
