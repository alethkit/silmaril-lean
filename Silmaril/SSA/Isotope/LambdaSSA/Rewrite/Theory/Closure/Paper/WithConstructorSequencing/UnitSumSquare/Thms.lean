module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare

/-! # Square reflection and uniformity on finite unit coproducts -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.BoundSimulation (boundReturn)
open Paper.UnaryReturn.Beta.Constructors (Normalizes)
open scoped Paper.BoundSimulation.Obstruction

/-- A table restricts to its specified arrow on each unit summand. -/
theorem inj_table (A : Shape) {X : Paper.TypeCategory Empty} (rows : A.Row → (obj .unit ⟶ X))
    (i : A.Row) : A.inj i ≫ A.table rows = rows i :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.inj_table A rows i

/-- The unit summand injections jointly determine an arrow in standard Paper. -/
theorem table_hom_ext (A : Shape) {X : Paper.TypeCategory Empty} {f g : obj A.ty ⟶ X}
    (h : ∀ i : A.Row, A.inj i ≫ f = A.inj i ≫ g) : f = g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.table_hom_ext A h

/-- Projected equality of literal outputs implies equality of their row codes. -/
theorem separate_output (B A : Shape) {i j : Sum B.Row A.Row}
    (h : projection.map (output B A i) = projection.map (output B A j)) : i = j :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.separate_output B A h

/-- A projected square for these tables commutes in standard Paper. The source
rows and target rows in the image of the state map use literal outputs.
The state map is a single typed constructor return and may identify rows. -/
theorem reflect_square (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasLiteralTargets B A D ha q)
    (comm : projection.map (step B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha)) =
      projection.map (branch ha ≫ D.table q)) :
    step B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha) = branch ha ≫ D.table q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.reflect_square
    B A D ha p q hq comm

/-- Uniformity for guarded arrows with projected table representatives and literal
outputs on the source rows and reachable target rows.
The square uses the original bind-first state update; its constructor normal form
supplies the standard Paper representative after reflection. -/
theorem iterate_uniformity (B A D : Shape) {t c : Tm Empty}
    (hc : Normalizes [A.ty] t c D.ty)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasLiteralTargets B A D hc.typed.2 q)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (step B A p))
    (hg : projection.map g = projection.map (D.table q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (boundReturn hc.typed.1)) =
      projection.map (boundReturn hc.typed.1 ≫ g)) :
    projection.map (iterate f) =
      projection.map (boundReturn hc.typed.1) ≫ projection.map (iterate g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.iterate_uniformity
    B A D hc p q hq hf hg comm

namespace Collapse

/-- The constructor map sends two distinct injections to the same arrow. -/
theorem collapse_not_mono : ¬ Mono (branch normalizes.typed.2) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.Collapse.collapse_not_mono

/-- The two distinct self-loops simulate the single target self-loop. -/
theorem iterate_collapse :
    projection.map (iterate (step result source sourceRows)) =
      projection.map (boundReturn normalizes.typed.1) ≫
        projection.map (iterate (step result target targetRows)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.Collapse.iterate_collapse

end Collapse

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare
