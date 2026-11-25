module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts

/-! # Automatic cuts and uniformity for all-recurrent forwarding tables -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Automatic

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Termination (run forwardingRows)
open scoped Function Paper.BoundSimulation.Obstruction

/-- Choose one anchor per eventual cycle, mark its incoming cycle edge, and
obtain a common bound on the first marked edge for all orbits. -/
theorem exists_orbit_cut {X : Type*} [Finite X] (next : X → X) :
    ∃ (anchor : X → X) (mark : X → Bool) (bound : Nat),
      (∀ i, anchor (next i) = anchor i) ∧
      (∀ i, anchor (anchor i) = anchor i) ∧
      (∀ i, mark i = true ↔ i ∈ Function.periodicPts next ∧ next i = anchor i) ∧
      (∀ i j, anchor i = anchor j → mark i = true → mark j = true → i = j) ∧
      (∀ i, ∃ k < bound, mark (next^[k] i) = true) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts.exists_orbit_cut next

/-- The unit rows of every finite sum shape form a finite type. -/
theorem rows_finite (A : Shape) : Finite A.Row :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts.rows_finite A

/-- Every finite successor table has a cut to idempotent anchors with one
fuel bound valid for all input rows. -/
theorem exists_bounded_cut (B A : Shape) (next : A.Row → A.Row) :
    ∃ (mark : A.Row → Bool) (anchor : A.Row → A.Row) (fuel : Nat),
      (∀ i, anchor (anchor i) = anchor i) ∧
      (∀ i, run (cutRows B next mark) fuel i = some ⟨.inr (anchor i), .forward⟩) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts.exists_bounded_cut B A next

/-- An all-recurrent forwarding table folds to the singleton forwarding self-loop. -/
theorem iterate_fold (B A : Shape) (next : A.Row → A.Row) :
    iterate (stepWithPayload B A (recurrenceRows B next)) =
      fold A ≫ iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts.iterate_fold B A next

/-- Any forwarding case map transports iteration between all-recurrent
forwarding tables in standard Paper. -/
theorem iterate_case_uniformity (B A D : Shape) (tags : A.Row → D.Row)
    (nextA : A.Row → A.Row) (nextD : D.Row → D.Row) :
    iterate (stepWithPayload B A (recurrenceRows B nextA)) =
      caseMap A D (forwardingRows tags) ≫ iterate (stepWithPayload B D (recurrenceRows B nextD)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts.iterate_case_uniformity B A D tags nextA nextD

/-- The same uniformity for guarded arrows with projected all-recurrent
forwarding representatives. -/
theorem iterate_projected_case_uniformity (B A D : Shape) (tags : A.Row → D.Row)
    (nextA : A.Row → A.Row) (nextD : D.Row → D.Row)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A (recurrenceRows B nextA)))
    (hg : projection.map g = projection.map (stepWithPayload B D (recurrenceRows B nextD))) :
    projection.map (iterate f) =
      projection.map (caseMap A D (forwardingRows tags)) ≫ projection.map (iterate g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts.iterate_projected_case_uniformity
    B A D tags nextA nextD hf hg

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Automatic
