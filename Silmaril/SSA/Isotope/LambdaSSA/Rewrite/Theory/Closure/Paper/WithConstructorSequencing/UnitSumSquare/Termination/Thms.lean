module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination

/-! # Uniformity by bounded unfolding of terminating case tables -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Termination

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open scoped Paper.BoundSimulation.Obstruction

/-- A commuting square of row codes preserves bounded runs, including their
payload choices after the state map. -/
theorem run_simulates (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload)
    (n : Nat) (i : A.Row) :
    run p n i = (run q n (rows i).tag).map (withInput (rows i).payload) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.run_simulates B A D rows p q square n i

/-- A successful bounded run gives the corresponding row of categorical
iteration in standard Paper. -/
theorem iterate_run (B A : Shape) (p : A.Row → OutputCode B A) (n : Nat) (i : A.Row)
    {o : StateCode B} (h : run p n i = some o) :
    A.inj i ≫ iterate (stepWithPayload B A p) = B.emit o.tag o.payload :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.iterate_run B A p n i h

/-- Finite successful runs from the source rows suffice for iteration
uniformity in standard Paper, even for noninvertible case maps. -/
theorem iterate_case_uniformity_ofTerminates (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D) (terminates : Terminates p)
    (comm : projection.map (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ stepWithPayload B D q)) :
    iterate (stepWithPayload B A p) = caseMap A D rows ≫ iterate (stepWithPayload B D q) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.iterate_case_uniformity_ofTerminates
    B A D rows p q terminates comm

/-- Transport the terminating result to guarded arrows with projected coded tables. -/
theorem iterate_projected_ofTerminates (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D) (terminates : Terminates p)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A p))
    (hg : projection.map g = projection.map (stepWithPayload B D q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ g)) :
    projection.map (iterate f) =
      projection.map (caseMap A D rows) ≫ projection.map (iterate g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.iterate_projected_ofTerminates
    B A D rows p q terminates hf hg comm

/-- For a forwarding surjection and a commuting square, a middle arrow
exists exactly when the source step codes agree on each fiber. -/
theorem factorization_iff_fibers (B A D : Shape) (tags : A.Row → D.Row)
    (onto : Function.Surjective tags)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (comm : projection.map (stepWithPayload B A p ≫
        coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ stepWithPayload B D q)) :
    (∃ m : obj D.ty ⟶ obj B.ty ⨿ obj A.ty,
      stepWithPayload B A p = caseMap A D (forwardingRows tags) ≫ m ∧
      stepWithPayload B D q = m ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) ↔
    ∀ i j, tags i = tags j → p i = p j :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.factorization_iff_fibers
    B A D tags onto p q comm

namespace MergeFibers

local notation "k" => caseMap source target (forwardingRows tags)

theorem surjective_tags : Function.Surjective tags :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.MergeFibers.surjective_tags

/-- The source's distinct successors have the same image, so the square holds. -/
theorem projected_square :
    projection.map (stepWithPayload result source sourceRows ≫ coprod.map (𝟙 (obj result.ty)) k) =
      projection.map (k ≫ stepWithPayload result target targetRows) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.MergeFibers.projected_square

/-- The source step cannot factor through the state map. -/
theorem no_left_factor :
    ¬ ∃ m : obj target.ty ⟶ obj result.ty ⨿ obj source.ty,
      stepWithPayload result source sourceRows = k ≫ m :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.MergeFibers.no_left_factor

/-- The state map identifies distinct inputs while forwarding their payloads. -/
theorem not_mono : ¬ Mono k :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.MergeFibers.not_mono

/-- The two-row bound proves the iteration equation in standard Paper. -/
theorem iterate_merge :
    iterate (stepWithPayload result source sourceRows) =
      k ≫ iterate (stepWithPayload result target targetRows) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination.MergeFibers.iterate_merge

end MergeFibers

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Termination
