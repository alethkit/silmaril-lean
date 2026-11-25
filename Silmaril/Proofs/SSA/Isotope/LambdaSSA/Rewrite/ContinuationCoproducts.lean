module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Coproducts.Defs

/-! # Universal properties of empty and concatenated exit interfaces -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {X Y Z : ContinuationContext Φ Γ}

theorem empty_unique (f g : (ContinuationContext.empty : ContinuationContext Φ Γ) ⟶ Z) :
    f = g := by
  induction f, g using Quotient.inductionOn₂ with
  | _ σ υ =>
    apply ContinuationFamily.toHom_eq_iff.mpr
    intro i A hi
    have h := (List.getElem?_eq_some_iff.mp hi).1
    exact (Nat.not_lt_zero _ h).elim

private def appendFamily (σ : ContinuationFamily (Φ := Φ) Γ X.labels Z.labels)
    (υ : ContinuationFamily (Φ := Φ) Γ Y.labels Z.labels) :
    ContinuationFamily (Φ := Φ) Γ (X.append Y).labels Z.labels :=
  ⟨fun i => if i < X.labels.length then σ.val i else υ.val (i - X.labels.length), by
    intro i A hi
    change At (X.labels ++ Y.labels) i A at hi
    change ValueBranches (A :: Γ) (if i < X.labels.length then σ.val i else
      υ.val (i - X.labels.length)) Z.labels
    by_cases h : i < X.labels.length
    · rw [ite_eq_left h]
      rw [At, List.getElem?_append_left h] at hi
      exact σ.property hi
    · rw [ite_eq_right h]
      rw [At, List.getElem?_append_right (Nat.le_of_not_gt h)] at hi
      exact υ.property hi⟩

private theorem appendInl_comp_toHom
    (σ : ContinuationFamily (Φ := Φ) Γ (X.append Y).labels Z.labels) :
    X.appendInl Y ≫ σ.toHom =
      ContinuationFamily.toHom ⟨σ.val, fun _ _ hi => σ.property
        ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1).trans hi)⟩ := by
  change (ContinuationFamily.compose _ σ).toHom = _
  apply congrArg (ContinuationFamily.toHom (X := X) (Y := Z))
  exact Subtype.ext (compLSubst_id_left σ.val)

private theorem appendInr_comp_toHom
    (σ : ContinuationFamily (Φ := Φ) Γ (X.append Y).labels Z.labels) :
    X.appendInr Y ≫ σ.toHom =
      ContinuationFamily.toHom ⟨fun i => σ.val (X.labels.length + i), fun i _ hi => σ.property (by
        change At (X.labels ++ Y.labels) (X.labels.length + i) _
        rw [At, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        exact hi)⟩ := by
  change (ContinuationFamily.compose _ σ).toHom = _
  apply congrArg (ContinuationFamily.toHom (X := Y) (Y := Z))
  apply Subtype.ext
  funext i
  exact congrFun (compLSubst_id_left σ.val) (X.labels.length + i)

noncomputable def appendIsColimit (X Y : ContinuationContext Φ Γ) :
    IsColimit (BinaryCofan.mk (X.appendInl Y) (X.appendInr Y)) := by
  refine BinaryCofan.IsColimit.mk _
    (fun f g => (appendFamily f.out g.out).toHom) ?_ ?_ ?_
  · intro Z f g
    change X.appendInl Y ≫ (appendFamily f.out g.out).toHom = f
    refine Eq.trans ?_ (Quotient.out_eq f)
    rw [appendInl_comp_toHom]
    apply ContinuationFamily.toHom_eq_iff.mpr
    intro i A hi
    change SubstitutionEquiv (A :: Γ) (if i < X.labels.length then f.out.val i
      else g.out.val (i - X.labels.length)) (f.out.val i) Z.labels
    rw [ite_eq_left (List.getElem?_eq_some_iff.mp hi).1]
    exact .base (.refl (f.out.property hi).hasType)
  · intro Z f g
    change X.appendInr Y ≫ (appendFamily f.out g.out).toHom = g
    refine Eq.trans ?_ (Quotient.out_eq g)
    rw [appendInr_comp_toHom]
    apply ContinuationFamily.toHom_eq_iff.mpr
    intro i A hi
    change SubstitutionEquiv (A :: Γ) (if X.labels.length + i < X.labels.length then
      f.out.val (X.labels.length + i) else g.out.val (X.labels.length + i - X.labels.length))
      (g.out.val i) Z.labels
    rw [ite_eq_right (Nat.not_lt_of_ge (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]
    exact .base (.refl (g.out.property hi).hasType)
  · intro Z f g q hf hg
    obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
    change X.appendInl Y ≫ σ.toHom = f at hf
    change X.appendInr Y ≫ σ.toHom = g at hg
    rw [appendInl_comp_toHom] at hf
    rw [appendInr_comp_toHom] at hg
    have left := ContinuationFamily.toHom_eq_iff.mp (hf.trans (Quotient.out_eq f).symm)
    have right := ContinuationFamily.toHom_eq_iff.mp (hg.trans (Quotient.out_eq g).symm)
    apply ContinuationFamily.toHom_eq_iff.mpr
    intro i A hi
    change At (X.labels ++ Y.labels) i A at hi
    change SubstitutionEquiv (A :: Γ) (σ.val i) (if i < X.labels.length then f.out.val i
      else g.out.val (i - X.labels.length)) Z.labels
    by_cases h : i < X.labels.length
    · rw [ite_eq_left h]
      rw [At, List.getElem?_append_left h] at hi
      exact left hi
    · rw [ite_eq_right h]
      have hle := Nat.le_of_not_gt h
      rw [At, List.getElem?_append_right hle] at hi
      simpa only [Nat.add_sub_of_le hle] using right hi

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
