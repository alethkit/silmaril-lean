module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles

/-! # Uniformity of forwarding cycles with bounded cuts -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Termination (run forwardingRows)
open scoped Paper.BoundSimulation.Obstruction

/-- Identifying the inner and outer feedback labels restores the original table. -/
theorem collapse_cut (B A : Shape) (next : A.Row → A.Row) (mark : A.Row → Bool) :
    cutStep B A next mark ≫ coprod.desc (𝟙 (obj B.ty ⨿ obj A.ty)) coprod.inr =
      stepWithPayload B A (recurrenceRows B next) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.collapse_cut B A next mark

/-- Finite unfolding along a forwarding path identifies its first and last
rows of iteration, even when the path enters a cycle. -/
theorem iterate_row_along (B A : Shape) (p : A.Row → OutputCode B A) {i j : A.Row}
    (path : Relation.ReflTransGen (fun src dst => p src = ⟨.inr dst, .forward⟩) i j) :
    A.inj i ≫ iterate (stepWithPayload B A p) = A.inj j ≫ iterate (stepWithPayload B A p) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.iterate_row_along B A p path

/-- A bounded cut that leads each row to a stable anchor reduces the original
forwarding loop to the singleton self-loop. -/
theorem iterate_fold_ofCut (B A : Shape) (next : A.Row → A.Row) (mark : A.Row → Bool)
    (anchor : A.Row → A.Row) (stable : ∀ i, anchor (anchor i) = anchor i)
    (bounded : ∀ i, ∃ n, run (cutRows B next mark) n i = some ⟨.inr (anchor i), .forward⟩) :
    iterate (stepWithPayload B A (recurrenceRows B next)) =
      fold A ≫ iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.iterate_fold_ofCut
    B A next mark anchor stable bounded

/-- Forwarding case maps transport iteration between two all-recurrent tables
with bounded cuts to stable anchors. -/
theorem iterate_case_uniformity_ofCuts (B A D : Shape) (tags : A.Row → D.Row)
    (nextA : A.Row → A.Row) (nextD : D.Row → D.Row)
    (markA : A.Row → Bool) (markD : D.Row → Bool)
    (anchorA : A.Row → A.Row) (anchorD : D.Row → D.Row)
    (stableA : ∀ i, anchorA (anchorA i) = anchorA i)
    (stableD : ∀ i, anchorD (anchorD i) = anchorD i)
    (boundedA : ∀ i, ∃ n, run (cutRows B nextA markA) n i = some ⟨.inr (anchorA i), .forward⟩)
    (boundedD : ∀ i, ∃ n, run (cutRows B nextD markD) n i = some ⟨.inr (anchorD i), .forward⟩) :
    iterate (stepWithPayload B A (recurrenceRows B nextA)) =
      caseMap A D (forwardingRows tags) ≫ iterate (stepWithPayload B D (recurrenceRows B nextD)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.iterate_case_uniformity_ofCuts
    B A D tags nextA nextD markA markD anchorA anchorD stableA stableD boundedA boundedD

namespace Alternate

/-- The alternating loop projects to the singleton self-loop. -/
theorem projected_square :
    projection.map (stepWithPayload result state (recurrenceRows result next) ≫
        coprod.map (𝟙 (obj result.ty)) (fold state)) =
      projection.map (fold state ≫ stepWithPayload result .unit (recurrenceRows result id)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.Alternate.projected_square

/-- The two source steps choose different successors in the same fiber, so
the square has no common middle arrow for rolling. -/
theorem no_factorization :
    ¬ ∃ m : obj .unit ⟶ obj result.ty ⨿ obj state.ty,
      stepWithPayload result state (recurrenceRows result next) = fold state ≫ m ∧
      stepWithPayload result .unit (recurrenceRows result id) =
        m ≫ coprod.map (𝟙 (obj result.ty)) (fold state) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.Alternate.no_factorization

/-- The fold identifies two distinct source rows. -/
theorem not_mono : ¬ Mono (fold state) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.Alternate.not_mono

/-- The two-cycle and its folded self-loop agree in standard Paper. -/
theorem iterate_cycle :
    iterate (stepWithPayload result state (recurrenceRows result next)) =
      fold state ≫ iterate (stepWithPayload result .unit (recurrenceRows result id)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.Alternate.iterate_cycle

/-- Two forwarding steps unfold the transient row to the right cycle row. -/
theorem transient_restriction :
    withTransient.inj (.inr ()) ≫
        iterate (stepWithPayload result withTransient (recurrenceRows result nextWithTransient)) =
      withTransient.inj (.inl (.inr ())) ≫
        iterate (stepWithPayload result withTransient (recurrenceRows result nextWithTransient)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.Alternate.transient_restriction

/-- The larger table, including the transient row, has the same folded iteration. -/
theorem iterate_withTransient :
    iterate (stepWithPayload result withTransient (recurrenceRows result nextWithTransient)) =
      fold withTransient ≫ iterate (stepWithPayload result .unit (recurrenceRows result id)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles.Alternate.iterate_withTransient

end Alternate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles
