module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Signature.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ResetTablesMultipleExample

/-! # Checked example with a folded cycle and a later reset on exit -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple.Example

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open ForwardingTables (obj)
open UnitSumSquare.Cycles.Mixed.MergeCycle (result source target)
open UnitSumSquare.Cycles.Payloads.ResetCycle (mark)
open scoped Paper.BoundSimulation.Obstruction

/-- The two closed assignments of the example remain distinguishable after projection. -/
theorem distinct_actions :
    projection.map (action (Φ := Empty) P (some left)) ≠ projection.map (action P (some right)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleExample.distinct_actions

/-- The state map merges two rows of the alternating cycle. -/
theorem not_mono : ¬ Mono (stateMap P source target stateRows) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleExample.not_mono

/-- The second assignment in the completed lap wins. -/
theorem cycle_last_reset :
    run (cutRows sourceSteps mark) 2 (.inl (.inl ())) =
      some ⟨.inr (.inl (.inl ())), some right⟩ := rfl

/-- The exit assignment replaces the earlier reset on the terminating path. -/
theorem exit_last_reset :
    run sourceSteps 2 (.inr (.inl ())) = some ⟨(), some right⟩ := rfl

/-- The mixed square holds after constructor-sequencing projection. -/
theorem projected_square :
    projection.map (step P result source sourceSteps ≫
      coprod.map (𝟙 (obj P result)) (stateMap P source target stateRows)) =
    projection.map (stateMap P source target stateRows ≫ step P result target targetSteps) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleExample.projected_square

/-- The iteration equality holds in standard Paper for the noninjective state map. -/
theorem iterate_merge :
    iterate (step P result source sourceSteps) =
      stateMap P source target stateRows ≫ iterate (step P result target targetSteps) :=
  iterate_of_projected_square P result source target stateRows sourceSteps targetSteps projected_square

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple.Example
