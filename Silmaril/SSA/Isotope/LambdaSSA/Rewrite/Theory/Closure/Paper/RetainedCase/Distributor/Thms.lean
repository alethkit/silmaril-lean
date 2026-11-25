module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor

/-! # Distributor computations in the Paper singleton quotient -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open CfgEta.TypeCategory (caseValueBranches)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X A B : τ}

/-- The literal distributor carries the left input injection to the left output injection. -/
theorem left_distributor_inl (X A B : τ) :
    whiskerLeft (τ := τ) (ofType (Φ := Φ) X) (sumCofan (Φ := Φ) A B).inl ≫
      ofRegion (τ := τ) (distributorRegion_typed X A B) =
        (sumCofan (Φ := Φ) (Silmaril.product X A) (Silmaril.product X B)).inl :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor.left_distributor_inl X A B

/-- The literal distributor carries the right input injection to the right output injection. -/
theorem left_distributor_inr (X A B : τ) :
    whiskerLeft (τ := τ) (ofType (Φ := Φ) X) (sumCofan (Φ := Φ) A B).inr ≫
      ofRegion (τ := τ) (distributorRegion_typed X A B) =
        (sumCofan (Φ := Φ) (Silmaril.product X A) (Silmaril.product X B)).inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor.left_distributor_inr X A B

/-- The literal packed copair restricts to its left arm. -/
theorem case_ofRegion_inl {D : τ} {p q : Region Φ} (hp : ValueBranches [A] p [D])
    (hq : ValueBranches [B] q [D]) :
    (sumCofan (Φ := Φ) A B).inl ≫ ofRegion (τ := τ) (caseValueBranches hp hq) = ofRegion (τ := τ) hp :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor.case_ofRegion_inl hp hq

/-- The literal packed copair restricts to its right arm. -/
theorem case_ofRegion_inr {D : τ} {p q : Region Φ} (hp : ValueBranches [A] p [D])
    (hq : ValueBranches [B] q [D]) :
    (sumCofan (Φ := Φ) A B).inr ≫ ofRegion (τ := τ) (caseValueBranches hp hq) = ofRegion (τ := τ) hq :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor.case_ofRegion_inr hp hq

/-- The literal distributor is invertible. Its inverse dispatches the tagged pair and restores its tag. -/
noncomputable def distributorIso (X A B : τ) :
    ofType (Φ := Φ) (Silmaril.product X (Silmaril.coprod A B)) ≅
      ofType (Silmaril.coprod (Silmaril.product X A) (Silmaril.product X B)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor.distributorIso X A B

/-- The two whiskered injections detect equality of arrows out of the retained sum. -/
theorem distributor_hom_ext {D : τ} {X A B : τ}
    {f g : ofType (Φ := Φ) (Silmaril.product X (Silmaril.coprod A B)) ⟶ ofType D}
    (hl : whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inl ≫ f =
      whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inl ≫ g)
    (hr : whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inr ≫ f =
      whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inr ≫ g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor.distributor_hom_ext hl hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase
