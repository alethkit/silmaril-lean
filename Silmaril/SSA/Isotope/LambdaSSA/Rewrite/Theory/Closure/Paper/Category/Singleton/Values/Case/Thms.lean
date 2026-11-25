module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseInterchange

/-! # Interchange of case arrows from the two arm equations -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B D X Y : τ}

/-- Right-whiskered sum injections detect equality by transporting
the checked left distributor along the guarded swap. -/
theorem rightWhiskeredSum_hom_ext
    {f g : ofType (Φ := Φ) (product (coprod A B) X) ⟶ ofType D}
    (hl : whiskerRight (sumCofan (Φ := Φ) A B).inl (ofType X) ≫ f =
      whiskerRight (sumCofan (Φ := Φ) A B).inl (ofType X) ≫ g)
    (hr : whiskerRight (sumCofan (Φ := Φ) A B).inr (ofType X) ≫ f =
      whiskerRight (sumCofan (Φ := Φ) A B).inr (ofType X) ≫ g) : f = g :=
  CaseInterchange.rightWhiskeredSum_hom_ext hl hr

/-- The right-factor square of a case follows from the two arm squares. -/
theorem sum_interchange_right
    (f : ofType (Φ := Φ) (coprod A B) ⟶ ofType D) (k : ofType X ⟶ ofType Y)
    (hl : whiskerLeft (ofType X) ((sumCofan A B).inl ≫ f) ≫ whiskerRight k (ofType D) =
      whiskerRight k (ofType A) ≫ whiskerLeft (ofType Y) ((sumCofan A B).inl ≫ f))
    (hr : whiskerLeft (ofType X) ((sumCofan A B).inr ≫ f) ≫ whiskerRight k (ofType D) =
      whiskerRight k (ofType B) ≫ whiskerLeft (ofType Y) ((sumCofan A B).inr ≫ f)) :
    whiskerLeft (ofType X) f ≫ whiskerRight k (ofType D) =
      whiskerRight k (ofType (coprod A B)) ≫ whiskerLeft (ofType Y) f :=
  CaseInterchange.sum_interchange_right f k hl hr

/-- The left-factor square of a case follows from the two arm squares. -/
theorem sum_interchange_left
    (f : ofType (Φ := Φ) (coprod A B) ⟶ ofType D) (k : ofType X ⟶ ofType Y)
    (hl : whiskerRight ((sumCofan A B).inl ≫ f) (ofType X) ≫ whiskerLeft (ofType D) k =
      whiskerLeft (ofType A) k ≫ whiskerRight ((sumCofan A B).inl ≫ f) (ofType Y))
    (hr : whiskerRight ((sumCofan A B).inr ≫ f) (ofType X) ≫ whiskerLeft (ofType D) k =
      whiskerLeft (ofType B) k ≫ whiskerRight ((sumCofan A B).inr ≫ f) (ofType Y)) :
    whiskerRight f (ofType X) ≫ whiskerLeft (ofType D) k =
      whiskerLeft (ofType (coprod A B)) k ≫ whiskerRight f (ofType Y) :=
  CaseInterchange.sum_interchange_left f k hl hr

/-- Both squares of an exact copair follow from the two arms being central. -/
theorem whiskerCentral_sumCofan_desc

    (l : ofType (Φ := Φ) A ⟶ ofType D) (r : ofType (Φ := Φ) B ⟶ ofType D)
    (hl : WhiskerCentral l) (hr : WhiskerCentral r) :
    WhiskerCentral ((sumIso A B).hom ≫ coprod.desc l r) :=
  CaseInterchange.whiskerCentral_sumCofan_desc l r hl hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
