module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Example.Thms

/-! # State-changing uniformity in the constructor sequencing quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.Example

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Paper.TypeCategory (iterate)
open Paper.BoundSimulation (boundReturn)
open RetainedLet (returnOnce returnOnce_typed)
open UnaryReturn.Beta.Constructors.Example
open scoped Paper.BoundSimulation.Obstruction

/-- The update normalizes at the concrete state-changing interface. -/
theorem update_eq_constructor :
    Eqv [source] (returnOnce update) (.br 0 constructor) [target] :=
  returnOnce_eq_branch update_normalizes

theorem update_arrow_eq_constructor :
    projection.map (boundReturn update_normalizes.typed.1) = projection.map constructorArrow :=
  (Extension.Singleton.ofRegion_eq_iff Seed (returnOnce_typed update_normalizes.typed.1)
    (.br (ℓ := 0) rfl update_normalizes.typed.2)).2 update_eq_constructor

/-- Both the recurrent and outward paths use the default square at the
constructor representative. The quotient supplies the sequencing equations. -/
theorem iterate_uniformity :
    projection.map (iterate sourceStep) =
      projection.map (boundReturn update_normalizes.typed.1) ≫
        projection.map (iterate targetStep) :=
  fixture_uniform (fun e => .inl e) constructorSequencing

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.Example
