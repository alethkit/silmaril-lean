module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionRenaming
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionTensor

/-! # Selecting entries of an interpreted quantitative substitution -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

private theorem split_projection_aux {X L R G : τ} (hX : X = Silmaril.unit)
    (d : M.Hom L X) (hd : M.hasEffect ⊥ d) (hL : Quantity.affine ≤ quantity L)
    (z : M.Hom R (product X R)) (hz : HEq z (M.leftUnitorInv R))
    (w : M.Hom G R) (s : M.Hom G (product L R))
    (hs : M.compose w z = M.compose s (M.tensor d (M.identity R))) :
    M.compose s (M.compose (M.right (M.discard L hL) R) (M.leftUnitor R)) = w := by
  subst X
  cases eq_of_heq hz
  rw [M.pure_to_unit_unique d hd hL] at hs
  simp only [SeqData.tensor, M.toSeqData.left_identity, M.toSeqData.compose_identity] at hs
  have he := congrArg (fun k => M.compose k (M.leftUnitor R)) hs
  simpa only [M.toSeqData.compose_assoc, M.toSeqData.leftUnitor_inv_hom,
    M.toSeqData.compose_identity] using he.symm

/-- Dropping the left context output is the native weakening to the right output. -/
theorem split_weakenRight {n : Nat} {Γ Γl Γr : QCtx τ n}
    (s : Γ.Split Γl Γr) (hd : Γl.Discardable) :
    M.compose (split M.toSeqData s)
      (M.compose (M.right (discard M.toSeqData hd) (packed Γr)) (M.leftUnitor (packed Γr))) =
      weaken M.toSeqData (s.weakenRight hd) := by
  let wl : QCtx.Weakening Γl Γr.zero id := .ofPointwise
    (fun i => (s i).2.1.trans (s i).1.symm) (fun i => hd i)
  have hs := weaken_split M (s.weakenRight hd) s (QCtx.Split.zero_left Γr)
    wl (QCtx.Weakening.refl Γr)
  rw [weaken_refl] at hs
  exact split_projection_aux M (packed_zero Γr) (weaken M.toSeqData wl) (weaken_pure _ _)
    (discardable_quantity hd) (split M.toSeqData (QCtx.Split.zero_left Γr))
    (split_zero_left M.toSeqData Γr) (weaken M.toSeqData (s.weakenRight hd))
    (split M.toSeqData s) hs

private theorem split_projection_left_aux {X L R G : τ} (hX : X = Silmaril.unit)
    (d : M.Hom R X) (hd : M.hasEffect ⊥ d) (hR : Quantity.affine ≤ quantity R)
    (z : M.Hom L (product L X)) (hz : HEq z (M.rightUnitorInv L))
    (w : M.Hom G L) (s : M.Hom G (product L R))
    (hs : M.compose w z = M.compose s (M.tensor (M.identity L) d)) :
    M.compose s (M.compose (M.left L (M.discard R hR)) (M.rightUnitor L)) = w := by
  subst X
  cases eq_of_heq hz
  rw [M.pure_to_unit_unique d hd hR] at hs
  simp only [SeqData.tensor, M.toSeqData.right_identity, M.toSeqData.identity_compose] at hs
  have he := congrArg (fun k => M.compose k (M.rightUnitor L)) hs
  simpa only [M.toSeqData.compose_assoc, M.toSeqData.rightUnitor_inv_hom,
    M.toSeqData.compose_identity] using he.symm

/-- Dropping the right context output is the native weakening to the left output. -/
theorem split_weakenLeft {n : Nat} {Γ Γl Γr : QCtx τ n}
    (s : Γ.Split Γl Γr) (hd : Γr.Discardable) :
    M.compose (split M.toSeqData s)
      (M.compose (M.left (packed Γl) (discard M.toSeqData hd)) (M.rightUnitor (packed Γl))) =
      weaken M.toSeqData (s.weakenLeft hd) := by
  let wr : QCtx.Weakening Γr Γl.zero id := .ofPointwise
    (fun i => (s i).1.trans (s i).2.1.symm) (fun i => hd i)
  have hs := weaken_split M (s.weakenLeft hd) s (QCtx.Split.zero_right Γl)
    (QCtx.Weakening.refl Γl) wr
  rw [weaken_refl] at hs
  exact split_projection_left_aux M (packed_zero Γl) (weaken M.toSeqData wr) (weaken_pure _ _)
    (discardable_quantity hd) (split M.toSeqData (QCtx.Split.zero_right Γl))
    (split_zero_right M.toSeqData Γl) (weaken M.toSeqData (s.weakenLeft hd))
    (split M.toSeqData s) hs

end Silmaril.Isotope.Refinement.Models.Denotation

namespace Silmaril.Isotope.Refinement.Models.SeqData
open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem leftUnitor_natural {A B : τ} (f : M.Hom A B) :
    M.compose (M.left Silmaril.unit f) (M.leftUnitor B) =
      M.compose (M.leftUnitor A) f := by
  have he := congrArg (fun k => M.compose (M.leftUnitor A) k) (M.unit_bind f)
  simpa only [← M.compose_assoc, M.leftUnitor_hom_inv, M.identity_compose] using he

theorem rightUnitor_natural {A B : τ} (f : M.Hom A B) :
    M.compose (M.right f Silmaril.unit) (M.rightUnitor B) =
      M.compose (M.rightUnitor A) f := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [compose, right, rightUnitor, Category.assoc, eqToHom_trans_assoc]
  rw [PremonoidalCategory.whiskerRight_eqToHom_assoc f M.tensor_unit.symm]
  simp [PremonoidalCategory.rightUnitor_naturality]

/-- Discarding the first output of a tensor leaves the second computation. -/
theorem tensor_discard_left {A B D : τ} (f : M.Hom A B)
    (hD : Quantity.affine ≤ quantity D) :
    M.compose (M.tensor (M.discard D hD) f) (M.leftUnitor B) =
      M.compose (M.compose (M.right (M.discard D hD) A) (M.leftUnitor A)) f := by
  rw [tensor, M.compose_assoc, M.leftUnitor_natural, M.compose_assoc]

/-- Discarding the second output commutes past a retained computation. -/
theorem tensor_discard_right {A B D : τ} (f : M.Hom A B)
    (hD : Quantity.affine ≤ quantity D) :
    M.compose (M.tensor f (M.discard D hD)) (M.rightUnitor B) =
      M.compose (M.compose (M.left A (M.discard D hD)) (M.rightUnitor A)) f := by
  rw [tensor, M.exchange_right_pure _ _ (M.discard_pure D hD),
    M.compose_assoc, M.rightUnitor_natural, M.compose_assoc]

end Silmaril.Isotope.Refinement.Models.SeqData
