module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms

/-! # Restrict mixed case interchange equations to the two tags -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseInterchange

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Region.Paper (TypeCategory)
open Region.Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

private theorem sum_inl_central (A B : τ) :
    WhiskerCentral (sumCofan (Φ := Φ) A B).inl := by
  rw [sumCofan_inl]
  exact whiskerCentral_ofRegion_branchValue (.inl (.var rfl))

private theorem sum_inr_central (A B : τ) :
    WhiskerCentral (sumCofan (Φ := Φ) A B).inr := by
  rw [sumCofan_inr]
  exact whiskerCentral_ofRegion_branchValue (.inr (.var rfl))

private theorem right_square_precomp {I S D X Y : Comp}
    (i : I ⟶ S) (f : S ⟶ D) (k : X ⟶ Y)
    (hi : whiskerLeft X i ≫ whiskerRight k S = whiskerRight k I ≫ whiskerLeft Y i)
    (hf : whiskerLeft X (i ≫ f) ≫ whiskerRight k D =
      whiskerRight k I ≫ whiskerLeft Y (i ≫ f)) :
    whiskerLeft X i ≫ (whiskerLeft X f ≫ whiskerRight k D) =
      whiskerLeft X i ≫ (whiskerRight k S ≫ whiskerLeft Y f) := by
  rw [← Category.assoc, ← whiskerLeft_comp, hf, whiskerLeft_comp, ← Category.assoc, ← hi, Category.assoc]

private theorem left_square_precomp {I S D X Y : Comp}
    (i : I ⟶ S) (f : S ⟶ D) (k : X ⟶ Y)
    (hi : whiskerRight i X ≫ whiskerLeft S k = whiskerLeft I k ≫ whiskerRight i Y)
    (hf : whiskerRight (i ≫ f) X ≫ whiskerLeft D k =
      whiskerLeft I k ≫ whiskerRight (i ≫ f) Y) :
    whiskerRight i X ≫ (whiskerRight f X ≫ whiskerLeft D k) =
      whiskerRight i X ≫ (whiskerLeft S k ≫ whiskerRight f Y) := by
  rw [← Category.assoc, ← whiskerRight_comp, hf, whiskerRight_comp, ← Category.assoc, ← hi, Category.assoc]

theorem sum_interchange_right {A B D X Y : τ}
    (f : ofType (Φ := Φ) (coprod A B) ⟶ ofType D) (k : ofType X ⟶ ofType Y)
    (hl : whiskerLeft (ofType X) ((sumCofan A B).inl ≫ f) ≫ whiskerRight k (ofType D) =
      whiskerRight k (ofType A) ≫ whiskerLeft (ofType Y) ((sumCofan A B).inl ≫ f))
    (hr : whiskerLeft (ofType X) ((sumCofan A B).inr ≫ f) ≫ whiskerRight k (ofType D) =
      whiskerRight k (ofType B) ≫ whiskerLeft (ofType Y) ((sumCofan A B).inr ≫ f)) :
    whiskerLeft (ofType X) f ≫ whiskerRight k (ofType D) =
      whiskerRight k (ofType (coprod A B)) ≫ whiskerLeft (ofType Y) f :=
  Paper.RetainedCase.distributor_hom_ext
    (right_square_precomp (sumCofan A B).inl f k ((sum_inl_central A B k).2) hl)
    (right_square_precomp (sumCofan A B).inr f k ((sum_inr_central A B k).2) hr)

theorem rightWhiskeredSum_hom_ext {X A B D : τ}
    {f g : ofType (Φ := Φ) (product (coprod A B) X) ⟶ ofType D}
    (hl : whiskerRight (sumCofan (Φ := Φ) A B).inl (ofType X) ≫ f =
      whiskerRight (sumCofan (Φ := Φ) A B).inl (ofType X) ≫ g)
    (hr : whiskerRight (sumCofan (Φ := Φ) A B).inr (ofType X) ≫ f =
      whiskerRight (sumCofan (Φ := Φ) A B).inr (ofType X) ≫ g) : f = g := by
  apply (cancel_epi (braidIso (Φ := Φ) X (coprod A B)).hom).mp
  change braid X (coprod A B) ≫ f = braid X (coprod A B) ≫ g
  apply Paper.RetainedCase.distributor_hom_ext
  · erw [← Category.assoc, whiskerLeft_braid X (sumCofan (Φ := Φ) A B).inl,
      Category.assoc, hl, ← Category.assoc, ← whiskerLeft_braid X (sumCofan (Φ := Φ) A B).inl,
      Category.assoc]
    rfl
  · erw [← Category.assoc, whiskerLeft_braid X (sumCofan (Φ := Φ) A B).inr,
      Category.assoc, hr, ← Category.assoc, ← whiskerLeft_braid X (sumCofan (Φ := Φ) A B).inr,
      Category.assoc]
    rfl

theorem sum_interchange_left {A B D X Y : τ}
    (f : ofType (Φ := Φ) (coprod A B) ⟶ ofType D) (k : ofType X ⟶ ofType Y)
    (hl : whiskerRight ((sumCofan A B).inl ≫ f) (ofType X) ≫ whiskerLeft (ofType D) k =
      whiskerLeft (ofType A) k ≫ whiskerRight ((sumCofan A B).inl ≫ f) (ofType Y))
    (hr : whiskerRight ((sumCofan A B).inr ≫ f) (ofType X) ≫ whiskerLeft (ofType D) k =
      whiskerLeft (ofType B) k ≫ whiskerRight ((sumCofan A B).inr ≫ f) (ofType Y)) :
    whiskerRight f (ofType X) ≫ whiskerLeft (ofType D) k =
      whiskerLeft (ofType (coprod A B)) k ≫ whiskerRight f (ofType Y) :=
  rightWhiskeredSum_hom_ext (X := X)
    (left_square_precomp (sumCofan A B).inl f k ((sum_inl_central A B k).1) hl)
    (left_square_precomp (sumCofan A B).inr f k ((sum_inr_central A B k).1) hr)

theorem whiskerCentral_sumCofan_desc {A B D : τ}

    (l : ofType (Φ := Φ) A ⟶ ofType D) (r : ofType (Φ := Φ) B ⟶ ofType D)
    (hl : WhiskerCentral l) (hr : WhiskerCentral r) :
    WhiskerCentral ((sumIso A B).hom ≫ coprod.desc l r) := by
  have inl : (sumCofan (Φ := Φ) A B).inl ≫ ((sumIso A B).hom ≫ coprod.desc l r) = l :=
    (Category.assoc (sumCofan (Φ := Φ) A B).inl (sumIso A B).hom (coprod.desc l r)).symm.trans
      ((sumCofan_inl_sumIso_hom_assoc (Φ := Φ) A B (coprod.desc l r)).trans (coprod.inl_desc _ _))
  have inr : (sumCofan (Φ := Φ) A B).inr ≫ ((sumIso A B).hom ≫ coprod.desc l r) = r :=
    (Category.assoc (sumCofan (Φ := Φ) A B).inr (sumIso A B).hom (coprod.desc l r)).symm.trans
      ((sumCofan_inr_sumIso_hom_assoc (Φ := Φ) A B (coprod.desc l r)).trans (coprod.inr_desc _ _))
  intro X Y k
  refine ⟨sum_interchange_left (X := (show τ from X)) (Y := (show τ from Y)) _ k ?_ ?_,
    sum_interchange_right (X := (show τ from X)) (Y := (show τ from Y)) _ k ?_ ?_⟩
  · erw [inl]
    exact (hl k).1
  · erw [inr]
    exact (hr k).1
  · erw [inl]
    exact (hl k).2
  · erw [inr]
    exact (hr k).2

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseInterchange
