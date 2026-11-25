module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Distributive.Defs
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedDistributivity

/-! # Distributivity of the projected singleton tensor -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CoproductDistributivity

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "Q" => TypeCategory Seed

/-- The exact sum cocone stays a coproduct after the native fixed-left whisker. -/
noncomputable def whiskeredSumIsColimit (X A B : τ) :
    IsColimit (BinaryCofan.map (whiskerLeftFunctor Seed (ofType Seed X)) (sumCofan Seed A B)) :=
  ProjectedDistributivity.whiskeredSumIsColimit Seed X A B

/-- The native projected fixed-left whisker preserves binary coproducts. -/
theorem whiskerLeftPreservesBinary (X : Q) :
    PreservesColimitsOfShape (Discrete WalkingPair) (whiskerLeftFunctor Seed X) :=
  ProjectedDistributivity.whiskerLeftPreservesBinary Seed X

/-- A premonoidal structure with the same fixed-left whisker up to natural
isomorphism has the canonical categorical distributor. -/
theorem distributiveTensor_of_whisker [PremonoidalCategory Q]
    (agree : ∀ X : Q, Nonempty (whiskerLeftFunctor Seed X ≅ leftTensorFunctor Seed X)) :
    DistributiveTensor Q :=
  ProjectedDistributivity.distributiveTensor_of_whisker Seed agree

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CoproductDistributivity
