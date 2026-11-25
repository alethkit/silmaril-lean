module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Transport

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs

universe u v

variable {L : Type u} {R : Type v} {stepL : L → L → Prop} {stepR : R → R → Prop}
variable {relatedMarks : L → R → Prop}

private theorem last_related {n : Nat} {a a' : L} {b b' : R}
    (trace : PairedSteps stepL stepR relatedMarks n a b a' b') : relatedMarks a' b' := by
  cases trace <;> assumption

theorem pair_left
    (forth : ∀ {a a' b}, relatedMarks a b → stepL a a' → ∃ b', stepR b b' ∧ relatedMarks a' b')
    {n : Nat} {a a' : L} {b : R} (initially : relatedMarks a b) (trace : Steps stepL n a a') :
    ∃ b', PairedSteps stepL stepR relatedMarks n a b a' b' := by
  induction trace with
  | refl => exact ⟨_, .refl initially⟩
  | tail earlier last ih =>
    obtain ⟨_, paired⟩ := ih initially
    have ready := last_related paired
    obtain ⟨_, moved, related⟩ := forth ready last
    exact ⟨_, .tail paired last moved related⟩

theorem pair_right
    (back : ∀ {a b b'}, relatedMarks a b → stepR b b' → ∃ a', stepL a a' ∧ relatedMarks a' b')
    {n : Nat} {a : L} {b b' : R} (initially : relatedMarks a b) (trace : Steps stepR n b b') :
    ∃ a', PairedSteps stepL stepR relatedMarks n a b a' b' := by
  induction trace with
  | refl => exact ⟨_, .refl initially⟩
  | tail earlier last ih =>
    obtain ⟨_, paired⟩ := ih initially
    have ready := last_related paired
    obtain ⟨_, moved, related⟩ := back ready last
    exact ⟨_, .tail paired moved last related⟩

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs
