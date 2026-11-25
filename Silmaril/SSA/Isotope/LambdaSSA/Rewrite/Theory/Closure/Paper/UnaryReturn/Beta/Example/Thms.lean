module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Example

/-! # The unary-let obstruction in the fusion-only quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory Paper.UnaryReturn

theorem changeState_beta : BetaNormalizes [state] changeState .unit result :=
  .let₁ (.value (.var (i := 0) rfl)) (.value .unit)

theorem stateMap_eq_constructor :
    (Extension.Singleton.projection Step).map stateMap =
      (Extension.Singleton.projection Step).map
        (ofRegion (.br (ℓ := 0) rfl changeState_beta.branchValue)) :=
  changeState_beta.boundReturn_eq_constructor (fun e => e)

/-- The former uniformity witness satisfies the equation after unary return fusion. -/
theorem beta_uniformity :
    (Extension.Singleton.projection Step).map (iterate sourceStep) =
      (Extension.Singleton.projection Step).map stateMap ≫
        (Extension.Singleton.projection Step).map (iterate targetStep) :=
  changeState_beta.iterate_map_uniformity (fun e => e) rfl rfl
    (coprod.inr_map (𝟙 (ofType result)) (returnTerm changeState_beta.hasType))

/-- Constructor uniformity and unary return fusion also equate the original closed CFGs. -/
theorem beta_cfg_equality : Paper.Extension.Eqv Step [] before after [result] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.closed_cfg

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction
