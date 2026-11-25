module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Fixture

/-! # Separating equations in the default Paper presentation
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory

/-- The local square uses the default typed rewrite relation. -/
theorem local_square : Paper.Eqv [state] localSource localTarget [result, result] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.local_square

theorem categorical_square :
    sourceStep ≫ coprod.map (𝟙 (ofType result)) stateMap = stateMap ≫ targetStep :=
  coprod.inr_map (𝟙 (ofType result)) stateMap

/-- A commuting square for an instruction-free unary-let state change fails
to induce the uniformity equation in both forms of the default presentation.
The opt-in instruction-free simulation seed proves the closed CFG equation. -/
theorem separation :
    Paper.Eqv [state] localSource localTarget [result, result] ∧
    sourceStep ≫ coprod.map (𝟙 (ofType result)) stateMap = stateMap ≫ targetStep ∧
    (¬ Paper.Eqv [] before after [result]) ∧
    iterate sourceStep ≠ stateMap ≫ iterate targetStep ∧
    Paper.Extension.Eqv InstructionFreeStep [] before after [result] :=
  ⟨local_square, categorical_square,
    Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.default_uniformity_fails,
    Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.categorical_uniformity_fails,
    Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.opt_in_equality⟩

/-- Guarded unit η fails in default Paper, even with no instructions. -/
theorem unit_eta_fails :
    ¬ Paper.Eqv [(Ty.unit : Ty Empty)] (.br 0 (.unit : Tm Empty)) (.br 0 (.var 0)) [Ty.unit] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.unit_eta_fails

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction
