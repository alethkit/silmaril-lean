module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
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

/-- The observer distinguishes both the result tag and the unit payload choice. -/
theorem separate_payload_output (B A : Shape) {i j : OutputCode B A}
    (h : projection.map (outputWithPayload B A i) = projection.map (outputWithPayload B A j)) :
    i = j :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.separate_payload_output B A h

/-- Compare the composed square arms after restriction to their source rows.
A row may forward the input or emit literal unit. -/
theorem reflect_payload_square (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (p : A.Row → OutputCode B A) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasTargetOutputs B A D ha q)
    (comm : projection.map (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha)) =
      projection.map (branch ha ≫ D.table q)) :
    stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha) = branch ha ≫ D.table q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.reflect_payload_square
    B A D ha p q hq comm

/-- A projected square for guarded arrows with coded table representatives
gives uniformity for the original bind-first update. -/
theorem iterate_payload_uniformity (B A D : Shape) {t c : Tm Empty}
    (hc : Normalizes [A.ty] t c D.ty)
    (p : A.Row → OutputCode B A) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasTargetOutputs B A D hc.typed.2 q)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A p))
    (hg : projection.map g = projection.map (D.table q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (boundReturn hc.typed.1)) =
      projection.map (boundReturn hc.typed.1 ≫ g)) :
    projection.map (iterate f) =
      projection.map (boundReturn hc.typed.1) ≫ projection.map (iterate g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.iterate_payload_uniformity
    B A D hc p q hq hf hg comm

/-- Each input injection selects its declared branch of the case map. -/
theorem inj_caseMap (A D : Shape) (rows : A.Row → StateCode D) (i : A.Row) :
    A.inj i ≫ caseMap A D rows = D.emit (rows i).tag (rows i).payload :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.inj_caseMap A D rows i

/-- Reflect a projected square whose state change is a finite case table. The
target needs a coded output on each row selected by that table. -/
theorem reflect_case_square (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasCaseTargetOutputs B A D rows q)
    (comm : projection.map (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ D.table q)) :
    stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows) =
      caseMap A D rows ≫ D.table q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.reflect_case_square
    B A D rows p q hq comm

/-- When both step tables are coded, the projected square is equivalent to
pointwise equality of the two composed row codes. -/
theorem case_square_iff (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D) :
    projection.map (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
        projection.map (caseMap A D rows ≫ stepWithPayload B D q) ↔
      ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.case_square_iff
    B A D rows p q

/-- A bijection of the unit summands gives inverse case maps forwarding the payload. -/
noncomputable def permutationIso (A D : Shape) (e : A.Row ≃ D.Row) : obj A.ty ≅ obj D.ty :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.permutationIso A D e

@[simp] theorem permutationIso_hom (A D : Shape) (e : A.Row ≃ D.Row) :
    (permutationIso A D e).hom = caseMap A D (permutationRows e) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.permutationIso_hom A D e

/-- A reflected square for an invertible case map transports iteration by rolling. -/
theorem iterate_case_uniformity_ofIso (B A D : Shape) (rows : A.Row → StateCode D)
    (e : obj A.ty ≅ obj D.ty) (he : e.hom = caseMap A D rows)
    (p : A.Row → OutputCode B A) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasCaseTargetOutputs B A D rows q)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A p))
    (hg : projection.map g = projection.map (D.table q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ g)) :
    projection.map (iterate f) =
      projection.map (caseMap A D rows) ≫ projection.map (iterate g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.iterate_case_uniformity_ofIso
    B A D rows e he p q hq hf hg comm

namespace Forwarding

/-- The example forwards the payload through one recurrence and the outward exit. -/
theorem iterate_forwarding :
    projection.map (iterate (stepWithPayload result source sourceRows)) =
      projection.map (boundReturn normalizes.typed.1) ≫
        projection.map (iterate (stepWithPayload result target (targetRows .forward))) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.Forwarding.iterate_forwarding

/-- Replacing the target's forwarded exit payload by unit breaks the projected square. -/
theorem literal_square_fails :
    projection.map (stepWithPayload result source sourceRows ≫
      coprod.map (𝟙 (obj result.ty)) (boundReturn normalizes.typed.1)) ≠
      projection.map (boundReturn normalizes.typed.1 ≫ stepWithPayload result target (targetRows .literal)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.Forwarding.literal_square_fails

end Forwarding

namespace Swap

local notation "swapMap" => caseMap state state

/-- The swap is inequivalent in standard Paper to every constructor return
for either payload choice on its left branch. -/
theorem not_constructor_return (p : Payload) : ¬ ConstructorReturn (swapMap (stateRows p)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.Swap.not_constructor_return p

/-- Both the forwarding and mixed-payload swap commute with the recurrent step. -/
theorem projected_square (p : Payload) :
    projection.map (stepWithPayload result state (sourceRows p) ≫
      coprod.map (𝟙 (obj result.ty)) (swapMap (stateRows p))) =
      projection.map (swapMap (stateRows p) ≫ stepWithPayload result state targetRows) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.Swap.projected_square p

/-- Iteration commutes with the forwarding swap through its inverse case map. -/
theorem iterate_swap :
    projection.map (iterate (stepWithPayload result state (sourceRows .forward))) =
      projection.map (swapMap (stateRows .forward)) ≫
        projection.map (iterate (stepWithPayload result state targetRows)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare.Swap.iterate_swap

end Swap

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
