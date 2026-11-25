module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors.Example

/-! # A capture-free loop with both recurrence and an outward exit
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors.Example

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn Paper.RetainedLet
open Paper.TypeCategory Paper.BoundSimulation
open CategoryTheory CategoryTheory.Limits
open scoped Paper.BoundSimulation.Obstruction

theorem stepBody_typed :
    ValueBranches [target] stepBody [Silmaril.coprod (.unit : Ty Empty) source] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors.stepBody_typed

noncomputable def constructorArrow : ofType (Φ := Empty) source ⟶ ofType target :=
  ofRegion (.br (ℓ := 0) rfl update_normalizes.typed.2)

noncomputable def step : ofType (Φ := Empty) target ⟶
    ofType (.unit : Ty Empty) ⨿ ofType source :=
  ofRegion stepBody_typed ≫ (sumIso (.unit : Ty Empty) source).hom

noncomputable def sourceStep : ofType (Φ := Empty) source ⟶
    ofType (.unit : Ty Empty) ⨿ ofType source :=
  constructorArrow ≫ step

noncomputable def targetStep : ofType (Φ := Empty) target ⟶
    ofType (.unit : Ty Empty) ⨿ ofType target :=
  step ≫ coprod.map (𝟙 (ofType (.unit : Ty Empty))) constructorArrow

theorem fixture_uniform
    {Seed : VCtx (Ty Empty) → Region Empty → Region Empty → LCtx (Ty Empty) → Prop}
    (includeFusion : ∀ {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {r s : Region Empty},
      Step Γ r s L → Seed Γ r s L)
    (seq : ConstructorSequencing Seed) :
    (Paper.Extension.Singleton.projection Seed).map (iterate sourceStep) =
      (Paper.Extension.Singleton.projection Seed).map (boundReturn update_normalizes.typed.1) ≫
        (Paper.Extension.Singleton.projection Seed).map (iterate targetStep) :=
  update_normalizes.iterate_map_uniformity includeFusion seq rfl rfl (Category.assoc _ _ _)

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors.Example
