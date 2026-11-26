module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Thms

/-! # Steps that thread a fixed product factor through guarded feedback -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Comp" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe

attribute [local instance] computationPremonoidal computationSymmetric computationDistributive

/-- Keep the left factor on recursion and project it away on exit. -/
noncomputable abbrev retainLeftStep (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    R ⊗ A ⟶ B ⨿ (R ⊗ A) :=
  (R ◁ g ≫ DistributivePremonoidalCategory.leftInv R B A) ≫
    coprod.map (productSnd Seed R.as B.as) (𝟙 (R ⊗ A))

/-- The same step with the retained factor on the right. -/
noncomputable abbrev retainRightStep (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    A ⊗ R ⟶ B ⨿ (A ⊗ R) :=
  (braidIso Seed A R).hom ≫ retainLeftStep pe R g ≫ coprod.map (𝟙 B) (braidIso Seed A R).inv

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
