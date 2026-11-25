module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Directed

/-! # Deleting a computation while retaining its ambient input -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models
open CategoryTheory Denotation
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem rightUnitor_natural_pure {A B : τ} (f : M.Hom A B) (hf : M.hasEffect ⊥ f) :
    M.compose (M.rightUnitor A) f = M.compose (M.right f Silmaril.unit) (M.rightUnitor B) := by
  let A' : M.PureObject := ⟨A⟩
  let B' : M.PureObject := ⟨B⟩
  let ff : A' ⟶ B' := ⟨f, hf⟩
  exact congrArg Subtype.val (MonoidalCategory.rightUnitor_naturality ff).symm

theorem rightUnitor_product (A B : τ) :
    M.rightUnitor (product A B) =
      M.compose (M.associator A B Silmaril.unit) (M.left A (M.rightUnitor B)) := by
  let A' : M.PureObject := ⟨A⟩
  let B' : M.PureObject := ⟨B⟩
  have h : (ρ_ (A' ⊗ B')).hom = (α_ A' B' (𝟙_ M.PureObject)).hom ≫ A' ◁ (ρ_ B').hom := by
    monoidal
  exact congrArg Subtype.val h

/-- Regrouping a retained input isolates the part used by a deletable effect. -/
theorem retained_factor {G D E : τ} (s : M.Hom G (product D E))
    (hs : M.hasEffect ⊥ s) (t : M.Hom G (product G E))
    (c : M.Hom E (product E E))
    (h : M.compose t (M.compose (M.right s E) (M.associator D E E)) =
      M.compose s (M.left D c)) (a : M.Hom E Silmaril.unit) :
    M.compose (M.compose t (M.compose (M.left G a) (M.rightUnitor G))) s =
      M.compose s (M.left D (M.compose c (M.compose (M.left E a) (M.rightUnitor E)))) := by
  simp only [M.compose_assoc]
  rw [M.rightUnitor_natural_pure s hs]
  rw [← M.compose_assoc (M.left G a) (M.right s Silmaril.unit),
    ← M.exchange_left_pure s a hs]
  simp only [M.compose_assoc]
  rw [M.rightUnitor_product D E]
  rw [← M.compose_assoc (M.left (product D E) a), ← M.associator_natural_right]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.right s E), ← M.compose_assoc t, h]
  simp only [M.left_compose, M.compose_assoc]

end SeqData

namespace Denotation
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

theorem zero_unit_bind_aux {X D : τ} (hX : X = Silmaril.unit)
    (s : M.Hom D (product D X)) (hs : HEq s (M.rightUnitorInv D))
    (hd : Quantity.affine ≤ quantity X) :
    M.compose s (M.compose (M.left D (M.discard X hd)) (M.rightUnitor D)) = M.identity D := by
  subst X
  cases eq_of_heq hs
  rw [M.discard_unit, M.toSeqData.left_identity, M.toSeqData.identity_compose]
  exact M.toSeqData.rightUnitor_inv_hom D

/-- Binding a pure unit from a zero context performs no computation. -/
theorem zero_unit_bind {n : Nat} (Γ : QCtx τ n) (hd : Γ.zero.Discardable) :
    M.compose (split M.toSeqData (QCtx.Split.zero_right Γ))
      (M.compose (M.left (packed Γ) (discard M.toSeqData hd)) (M.rightUnitor (packed Γ))) =
      M.identity (packed Γ) :=
  zero_unit_bind_aux M (packed_zero Γ) _ (split_zero_right M.toSeqData Γ) _

/-- Native retention lets a computation be deleted without requiring the
entire ambient context to be affine or relevant. -/
theorem retained_elimination (p : Polarity) {e : ε} {n : Nat} {Γ Δ : QCtx τ n}
    (h : Γ.Split Δ Γ) (a : M.Hom (packed Δ) Silmaril.unit)
    (he : EffectSystem.canDelete p e) (ha : M.hasEffect e a) :
    p.orient M.le
      (M.compose (split M.toSeqData h.symm)
        (M.compose (M.left (packed Γ) a) (M.rightUnitor (packed Γ))))
      (M.identity (packed Γ)) := by
  let s := h.separate_retained
  have hc := h.relevant_retained
  have hs := split_assoc M.toSeqData h.symm s s (QCtx.Split.diagonal Δ hc)
  rw [split_diagonal M Δ hc] at hs
  have hf := M.toSeqData.retained_factor (split M.toSeqData s) (split_pure M.toSeqData s)
    (split M.toSeqData h.symm) (M.copy (packed Δ) (hc.trans (packed_quantity Δ))) hs a
  have hd := M.retained_unit_right p a (hc.trans (packed_quantity Δ)) he ha
  have hm := M.toSeqData.orient_compose_left p
    (M.toSeqData.orient_left p (packed (QCtx.complement Γ Δ)) hd) (split M.toSeqData s)
  rw [M.toSeqData.left_identity, M.toSeqData.compose_identity] at hm
  rw [← hf] at hm
  apply M.toSeqData.orient_of_compose_right p (split M.toSeqData s)
    (unsplitPure M.toSeqData s h.separate_retained_disjoint).val
    (split_unsplit M.toSeqData s h.separate_retained_disjoint)
  simpa only [M.toSeqData.identity_compose] using hm

end Denotation
end Silmaril.Isotope.Refinement.Models
