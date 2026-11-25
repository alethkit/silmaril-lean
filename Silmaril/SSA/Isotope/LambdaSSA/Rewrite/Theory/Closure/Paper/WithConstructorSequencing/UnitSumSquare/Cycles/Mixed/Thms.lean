module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles

/-! # Uniformity for mixed exit and recurrence forwarding tables -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Termination (run forwardingRows)
open scoped Paper.BoundSimulation.Obstruction

/-- A recurrence edge stays in the same termination class. -/
theorem reachesExit_step {B A : Shape} (p : A.Row → Sum B.Row A.Row) {i j : A.Row}
    (edge : p i = .inr j) : ReachesExit p i ↔ ReachesExit p j :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.reachesExit_step p edge

/-- A projected square preserves the outcome of every finite run. -/
theorem run_eq_of_square (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (stepWithPayload B A (forwardingSteps p) ≫
        coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ stepWithPayload B D (forwardingSteps q)))
    (n : Nat) (i : A.Row) :
    run (forwardingSteps p) n i = run (forwardingSteps q) n (tags i) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.run_eq_of_square B A D tags p q comm n i

/-- The state map of a projected square preserves the exit-reaching class. -/
theorem reachesExit_of_square (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (stepWithPayload B A (forwardingSteps p) ≫
        coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ stepWithPayload B D (forwardingSteps q)))
    (i : A.Row) : ReachesExit p i ↔ ReachesExit q (tags i) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.reachesExit_of_square B A D tags p q comm i

/-- The bounded cut sends each row to an exit or to a self-loop anchor
in the reduced tag table. -/
theorem exists_common_cut (B A : Shape) (p : A.Row → Sum B.Row A.Row) :
    ∃ (mark : A.Row → Bool) (fuel : Nat) (out : A.Row → Sum B.Row A.Row),
      (∀ i, run (forwardingSteps (cutTags p mark)) fuel i = some ⟨out i, .forward⟩) ∧
      (∀ i b, out i = .inl b → ReachesExit p i) ∧
      (∀ i j, out i = .inr j → ¬ ReachesExit p i ∧ out j = .inr j) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.exists_common_cut B A p

/-- The row of iteration at a nonterminating input is the singleton
forwarding self-loop. -/
theorem iterate_nonexit_row (B A : Shape) (p : A.Row → Sum B.Row A.Row) (i : A.Row)
    (infinite : ¬ ReachesExit p i) :
    A.inj i ≫ iterate (stepWithPayload B A (forwardingSteps p)) =
      iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.iterate_nonexit_row B A p i infinite

/-- Forwarding case-map uniformity for mixed exit and recurrence tables. -/
theorem iterate_case_uniformity (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (stepWithPayload B A (forwardingSteps p) ≫
        coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ stepWithPayload B D (forwardingSteps q))) :
    iterate (stepWithPayload B A (forwardingSteps p)) =
      caseMap A D (forwardingRows tags) ≫ iterate (stepWithPayload B D (forwardingSteps q)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.iterate_case_uniformity B A D tags p q comm

/-- Transport mixed-table uniformity along explicit projected representatives. -/
theorem iterate_projected_case_uniformity (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A (forwardingSteps p)))
    (hg : projection.map g = projection.map (stepWithPayload B D (forwardingSteps q)))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ g)) :
    projection.map (iterate f) =
      projection.map (caseMap A D (forwardingRows tags)) ≫ projection.map (iterate g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.iterate_projected_case_uniformity
    B A D tags p q hf hg comm

namespace MergeCycle

local notation "k" => caseMap source target (forwardingRows tags)

/-- A four-to-three square that merges a two-cycle and retains the exiting path. -/
theorem projected_square :
    projection.map (stepWithPayload result source (forwardingSteps sourceRows) ≫
        coprod.map (𝟙 (obj result.ty)) k) =
      projection.map (k ≫ stepWithPayload result target (forwardingSteps targetRows)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.MergeCycle.projected_square

/-- The alternating component has no exit. -/
theorem recurrent :
    ¬ ReachesExit sourceRows (.inl (.inl ())) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.MergeCycle.recurrent

/-- The other component reaches its exit after one recurrence. -/
theorem terminating : ReachesExit sourceRows (.inr (.inl ())) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.MergeCycle.terminating

/-- The fold identifies the two distinct cycle rows. -/
theorem not_mono : ¬ Mono k :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.MergeCycle.not_mono

/-- The distinct successor codes in one fiber rule out a rolling factor. -/
theorem no_factorization :
    ¬ ∃ m : obj target.ty ⟶ obj result.ty ⨿ obj source.ty,
      stepWithPayload result source (forwardingSteps sourceRows) = k ≫ m ∧
      stepWithPayload result target (forwardingSteps targetRows) =
        m ≫ coprod.map (𝟙 (obj result.ty)) k :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.MergeCycle.no_factorization

/-- The four-to-three iteration equation holds in standard Paper. -/
theorem iterate_merge :
    iterate (stepWithPayload result source (forwardingSteps sourceRows)) =
      k ≫ iterate (stepWithPayload result target (forwardingSteps targetRows)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles.MergeCycle.iterate_merge

end MergeCycle

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed
