module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.FiniteSquare.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.FiniteSquare

/-! # Reflection of a finite constructor-table square -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.FiniteSquare

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.BoundSimulation (boundReturn)
open scoped Paper.BoundSimulation.Obstruction

local notation "obj" => ofType (Φ := Empty)

/-- A projected square on the finite tables already commutes in Paper at the
constructor embedding. Only the two reachable target rows are constrained. -/
theorem reflect_square (p : Bool → Option Bool) (q : Bool → Option (Option Bool))
    (extra : obj U ⟶ obj U ⨿ obj D)
    (comm : projection.map (sourceStep p ≫ coprod.map (𝟙 (obj U)) embedding) =
      projection.map (embedding ≫ targetStep q extra)) :
    sourceStep p ≫ coprod.map (𝟙 (obj U)) embedding = embedding ≫ targetStep q extra :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.FiniteSquare.reflect_square
    p q extra comm

/-- Arbitrary guarded steps with the indicated projected representatives satisfy
uniformity when the square for the original bound update commutes after projection. -/
theorem iterate_uniformity (p : Bool → Option Bool) (q : Bool → Option (Option Bool))
    (extra : obj U ⟶ obj U ⨿ obj D)
    {f : obj S ⟶ obj U ⨿ obj S} {g : obj D ⟶ obj U ⨿ obj D}
    (hf : projection.map f = projection.map (sourceStep p))
    (hg : projection.map g = projection.map (targetStep q extra))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj U)) (boundReturn update_normalizes.typed.1)) =
      projection.map (boundReturn update_normalizes.typed.1 ≫ g)) :
    projection.map (iterate f) = projection.map (boundReturn update_normalizes.typed.1) ≫
      projection.map (iterate g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.FiniteSquare.iterate_uniformity
    p q extra hf hg comm

/-- The false state recurs to true, which exits. The additional target state
has its own self-loop, outside the image of the embedding. -/
theorem recur_then_exit :
    projection.map (iterate (sourceStep (fun b => if b then none else some true))) =
      projection.map (boundReturn update_normalizes.typed.1) ≫
        projection.map (iterate (targetStep (fun b => if b then none else some (some true))
          (targetOutput (some none)))) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.FiniteSquare.recur_then_exit

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.FiniteSquare
