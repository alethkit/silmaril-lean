module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.ProjectionExample.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionSimulation

/-! # From an ordinary projection square to a typed feedback equation -/

public section

universe u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.ProjectionExample

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory

theorem ordinary_square :
    repeatBefore ≫ coprod.map (𝟙 (ofType result)) stateChange = stateChange ≫ repeatAfter :=
  coprod.inr_map (𝟙 (ofType result)) stateChange

/-- Decode the chosen sum into repeat and outward labels, then reflect the
resulting arrow equality at the unique source label. -/
theorem local_square_of_ordinary
    (comm : repeatBefore ≫ coprod.map (𝟙 (ofType result)) stateChange = stateChange ≫ repeatAfter) :
    Paper.Eqv [state, state] repeatThenProject projectThenRepeat [payload, result] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionSimulation.local_square_of_ordinary comm

/-- The typed CFG equation in the contextual extension with instruction-free
simulation. The local square is a derivation in the original Paper relation. -/
theorem cfg_equation_of_ordinary
    (comm : repeatBefore ≫ coprod.map (𝟙 (ofType result)) stateChange = stateChange ≫ repeatAfter) :
    Paper.Extension.Eqv InstructionFreeStep [state] loopBefore loopAfter [result] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionSimulation.cfg_equation_of_ordinary comm

theorem cfg_equation :
    Paper.Extension.Eqv InstructionFreeStep [state] loopBefore loopAfter [result] :=
  cfg_equation_of_ordinary ordinary_square

/-- The same concrete CFGs give equal arrows in the shared opt-in singleton quotient. -/
theorem cfg_arrow_equation_of_ordinary
    (comm : repeatBefore ≫ coprod.map (𝟙 (ofType result)) stateChange = stateChange ≫ repeatAfter) :
    Paper.Extension.Singleton.ofRegion InstructionFreeStep loopBefore_valueBranches =
      Paper.Extension.Singleton.ofRegion InstructionFreeStep loopAfter_valueBranches :=
  (Paper.Extension.Singleton.ofRegion_eq_iff InstructionFreeStep _ _).2
    (cfg_equation_of_ordinary comm)

section Semantics

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel Types V) [InstructionModel J M Empty] [RegionTypingCoherent (Φ := Empty) J M]

/-- The contextual derivation has one denotation under the Paper model hypotheses. -/
theorem cfg_equation_denotes
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h) :
    ∃ f, RegionDenotes J M cfg_equation.typed.1 f ∧ RegionDenotes J M cfg_equation.typed.2 f :=
  cfg_equation.denotes J M shared (fun e => e.denotes J M shared)

end Semantics

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.ProjectionExample
