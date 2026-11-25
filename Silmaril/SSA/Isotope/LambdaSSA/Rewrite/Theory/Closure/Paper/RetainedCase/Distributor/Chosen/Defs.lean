module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Distributive.Defs

/-! # Transport of the guarded distributor to the chosen coproducts -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.Chosen

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

section Base
open Paper.TypeCategory (ofType sumIso whiskerLeftFunctor)

/-- The guarded distributor with both exact sums transported to the chosen coproducts. -/
noncomputable def paperChosenDistributor (X A B : τ) :
    ofType (Φ := Φ) (product X A) ⨿ ofType (product X B) ≅
      (whiskerLeftFunctor (ofType (Φ := Φ) X)).obj (ofType A ⨿ ofType B) :=
  (sumIso (product X A) (product X B)).symm ≪≫ (distributorIso X A B).symm ≪≫
    (whiskerLeftFunctor (ofType X)).mapIso (sumIso A B)

end Base

section Extension
open Paper.Extension.Singleton
open Paper.Extension.Singleton.CoproductDistributivity (leftTensorFunctor)

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "F" => projection Seed
set_option hygiene false in
local notation "L" => whiskerLeftFunctor Seed

/-- The same transport in a contextual singleton quotient. -/
noncomputable def projectedChosenDistributor (X A B : τ) :
    ofType Seed (product X A) ⨿ ofType Seed (product X B) ≅
      (L (ofType Seed X)).obj (ofType Seed A ⨿ ofType Seed B) :=
  (sumIso Seed (product X A) (product X B)).symm ≪≫ ((F).mapIso (distributorIso X A B)).symm ≪≫
    (L (ofType Seed X)).mapIso (sumIso Seed A B)

end Extension

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.Chosen
