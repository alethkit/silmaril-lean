module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Wires

public section

namespace Silmaril.RuntimeWires.Proofs.CollarAssociator

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {L M R A B C : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}
variable {f : ProgressiveGraph.Diagram S R C .point}
variable (m : d.OrderedVerticalMatch e) (n : e.OrderedVerticalMatch f)

abbrev LeftWires := Fin (wireCount (after m n).lowerJoin.glue f)
abbrev RightWires := Fin (wireCount (before m n).lowerJoin.glue n.glue)

@[expose] noncomputable def leftA (a : Fin A) : LeftWires m n := leftWire (after m n) (leftWire m a)
@[expose] noncomputable def leftB (b : Fin B) : LeftWires m n := leftWire (after m n) (rightWire m b)
@[expose] noncomputable def leftC (c : Fin C) : LeftWires m n := rightWire (after m n) c
@[expose] noncomputable def rightA (a : Fin A) : RightWires m n := leftWire (before m n) a
@[expose] noncomputable def rightB (b : Fin B) : RightWires m n := rightWire (before m n) (leftWire n b)
@[expose] noncomputable def rightC (c : Fin C) : RightWires m n := rightWire (before m n) (rightWire n c)

theorem leftAB (a : Contact d) : leftA m n a.val = leftB m n (m.contact a).val :=
  congrArg (leftWire (after m n)) (wire_contact m a)

theorem leftBC (b : Contact e) : leftB m n b.val = leftC m n (n.contact b).val := by
  have h := wire_contact (after m n) (outputCap m b)
  rw [outputCap_val, after_contact] at h
  exact h

theorem rightAB (a : Contact d) : rightA m n a.val = rightB m n (m.contact a).val := by
  have h := wire_contact (before m n) a
  rw [before_contact, inputCap_val] at h
  exact h

theorem rightBC (b : Contact e) : rightB m n b.val = rightC m n (n.contact b).val :=
  congrArg (rightWire (before m n)) (wire_contact n b)

@[expose] noncomputable def toRight : LeftWires m n → RightWires m n :=
  descend (after m n) (descend m (rightA m n) (rightB m n)) (rightC m n)

theorem toRight_A (a : Fin A) : toRight m n (leftA m n a) = rightA m n a := by
  unfold toRight leftA
  rw [descend_left, descend_left]

theorem toRight_B (b : Fin B) : toRight m n (leftB m n b) = rightB m n b := by
  unfold toRight leftB
  rw [descend_left, descend_right _ _ _ (rightAB m n)]

theorem toRight_C (c : Fin C) : toRight m n (leftC m n c) = rightC m n c := by
  unfold toRight leftC
  apply descend_right
  intro z
  let b := (outputCap m).symm z
  have eq : outputCap m b = z := (outputCap m).apply_symm_apply z
  rw [← eq, outputCap_val, after_contact, descend_right _ _ _ (rightAB m n)]
  exact rightBC m n b

@[expose] noncomputable def toLeft : RightWires m n → LeftWires m n :=
  descend (before m n) (leftA m n) (descend n (leftB m n) (leftC m n))

theorem toLeft_A (a : Fin A) : toLeft m n (rightA m n a) = leftA m n a := by
  unfold toLeft rightA
  rw [descend_left]

theorem agree_left (a : Contact d) :
    leftA m n a.val = descend n (leftB m n) (leftC m n) ((before m n).contact a).val := by
  rw [before_contact, inputCap_val, descend_left]
  exact leftAB m n a

theorem toLeft_B (b : Fin B) : toLeft m n (rightB m n b) = leftB m n b := by
  unfold toLeft rightB
  rw [descend_right _ _ _ (agree_left m n), descend_left]

theorem toLeft_C (c : Fin C) : toLeft m n (rightC m n c) = leftC m n c := by
  unfold toLeft rightC
  rw [descend_right _ _ _ (agree_left m n), descend_right _ _ _ (leftBC m n)]

theorem left_cases (w : LeftWires m n) :
    (∃ a, leftA m n a = w) ∨ (∃ b, leftB m n b = w) ∨ ∃ c, leftC m n c = w := by
  rcases wire_cases (after m n) w with ⟨i, eq⟩ | hc
  · rcases wire_cases m i with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact .inl ⟨a, eq⟩
    · exact .inr (.inl ⟨b, eq⟩)
  · exact .inr (.inr hc)

theorem right_cases (w : RightWires m n) :
    (∃ a, rightA m n a = w) ∨ (∃ b, rightB m n b = w) ∨ ∃ c, rightC m n c = w := by
  rcases wire_cases (before m n) w with ha | ⟨i, eq⟩
  · exact .inl ha
  · rcases wire_cases n i with ⟨b, rfl⟩ | ⟨c, rfl⟩
    · exact .inr (.inl ⟨b, eq⟩)
    · exact .inr (.inr ⟨c, eq⟩)

@[expose] noncomputable def wireEquiv : LeftWires m n ≃ RightWires m n where
  toFun := toRight m n
  invFun := toLeft m n
  left_inv w := by
    rcases left_cases m n w with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩
    · rw [toRight_A, toLeft_A]
    · rw [toRight_B, toLeft_B]
    · rw [toRight_C, toLeft_C]
  right_inv w := by
    rcases right_cases m n w with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩
    · rw [toLeft_A, toRight_A]
    · rw [toLeft_B, toRight_B]
    · rw [toLeft_C, toRight_C]

end Silmaril.RuntimeWires.Proofs.CollarAssociator
