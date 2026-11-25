module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ForwardingTablesClosed

/-! # Projected squares with instruction-free payloads -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ForwardingTables

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open UnitSumSquare (Shape)
open scoped Paper.BoundSimulation.Obstruction

/-- A closed input value distinguishes the two binary tags after projection. -/
theorem separates_of_closed {P : Ty Empty} {w : Tm Empty} (hw : Tm.BranchValue [] w P) :
    SeparatesTags (Φ := Empty) P :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed.separates_of_closed hw

/-- An instruction-free type with no closed constructor value is already initial in standard Paper. -/
theorem initial_of_no_closed_value (P : Ty Empty) (h : ¬ ∃ w : Tm Empty, Tm.BranchValue [] w P) :
    Nonempty (IsInitial (ofType (Φ := Empty) P)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed.initial_of_no_closed_value P h

/-- Every instruction-free type either separates tags or is initial.
The initial branch includes nested sums and products with no constructor inhabitants. -/
theorem separates_or_initial (P : Ty Empty) :
    SeparatesTags (Φ := Empty) P ∨ Nonempty (IsInitial (ofType (Φ := Empty) P)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed.separates_or_initial P

/-- The projected-square hypothesis suffices at every instruction-free payload type. -/
theorem iterate_of_instructionFree_square (P : Ty Empty) (B A D : Shape)
    (tags : A.Row → D.Row) (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (step (Φ := Empty) P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags)) =
      projection.map (stateMap P A D tags ≫ step P B D q)) :
    iterate (step (Φ := Empty) P B A p) = stateMap P A D tags ≫ iterate (step P B D q) :=
  iterate_of_projected_square P B A D tags p q (separates_or_initial P) comm

namespace ProductPayload

open UnitSumSquare.Cycles.Mixed.MergeCycle (result source target tags sourceRows targetRows)

/-- A product payload, with a sum-valued second field, forwarded unchanged on every branch. -/
abbrev payload : Ty Empty := .product .unit (.coprod .unit .unit)

/-- The four-row table folds a two-cycle to a self-loop and retains a separate exit path. -/
theorem projected_square :
    projection.map (step (Φ := Empty) payload result source sourceRows ≫
      coprod.map (𝟙 (obj payload result)) (stateMap payload source target tags)) =
    projection.map (stateMap payload source target tags ≫ step payload result target targetRows) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed.projected_square

/-- The state map identifies the two different cycle rows. -/
theorem not_mono : ¬ Mono (stateMap (Φ := Empty) payload source target tags) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed.not_mono

/-- The mixed table satisfies the iteration equation in standard Paper. -/
theorem iterate_merge :
    iterate (step (Φ := Empty) payload result source sourceRows) =
      stateMap payload source target tags ≫ iterate (step payload result target targetRows) :=
  iterate_of_instructionFree_square payload result source target tags sourceRows targetRows projected_square

end ProductPayload

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ForwardingTables
