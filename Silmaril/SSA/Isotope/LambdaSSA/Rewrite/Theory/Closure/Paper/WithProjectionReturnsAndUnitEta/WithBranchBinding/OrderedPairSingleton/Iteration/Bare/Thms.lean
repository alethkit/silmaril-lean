module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationObserver
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationSoundness

/-! # Bare feedback does not descend to the opt-in ordered-pair quotient

An effectful raw branch becomes a direct case scrutinee after bare label
substitution. Binding the branch first keeps that primitive in a unary let.
For this quotient a rewrite-invariant observation distinguishes the two
placements, even inside the feedback CFG. The unrestricted local commuting
equation is denotationally sound, but it would identify additional guarded
classes.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare

open Paper.TypeCategory.ITree.Reflection (Op payload Output)
open SyntacticCategory (iterationBody iterateRegion)

/-- The arbitrary-scrutinee dispatcher equation fails for the visible call. -/
theorem case_bind_separation :
    ¬ Extension.Eqv Seed [payload] (iterationBody rawStep)
      (iterationBody rawStep.bindBranchArguments) [payload, payload] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationObserver.case_bind_separation

/-- Both endpoints are guarded, so adjoining the equation would change guarded equality. -/
theorem case_bind_endpoints_guarded :
    ValueBranches [payload] (iterationBody rawStep) [payload, payload] ∧
      ValueBranches [payload] (iterationBody rawStep.bindBranchArguments) [payload, payload] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationObserver.case_bind_endpoints_guarded

/-- Closing the feedback label preserves the separation in this fixture. -/
theorem bare_iterate_separation :
    ¬ Extension.Eqv Seed [payload] (iterateRegion payload rawStep)
      (iterateRegion payload rawStep.bindBranchArguments) [payload] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationObserver.bare_iterate_separation

/-- Branch binding equates the input steps, but bare feedback fails to respect that equality. -/
theorem bare_iterate_not_congruent :
    ¬ (∀ {r s : Region Op}, Extension.Eqv Seed [payload] r s [Output] →
      Extension.Eqv Seed [payload] (iterateRegion payload r) (iterateRegion payload s) [payload]) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationObserver.bare_iterate_not_congruent

/-- On the effectful raw fixture, the bare output class differs from installed iteration. -/
theorem bare_iterate_ne_iterateSum :
    rawClass false (iterateRegion_typed rawStep_typed) ≠ iterateSum false (rawClass false rawStep_typed) :=
  fun h => bare_iterate_separation (Quotient.exact h)

section Soundness

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B : τ} {a : Tm Φ}
  {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- Binding the dispatcher scrutinee is sound as a standalone denotational equality.
This applies at arbitrary typed input contexts and allows an effectful sum scrutinee. -/
theorem denote_dispatch_bind (ha : Tm.HasType Γ a (coprod B A)) :
    denoteRegion J M (.let₁ ha
      (SyntacticCategory.iterationDispatch_valueBranches (Φ := Φ) A B).hasType) =
    denoteRegion J M (.case ha (.br (ℓ := 1) rfl (.var (i := 0) rfl))
      (.br (ℓ := 0) rfl (.var (i := 0) rfl)) : HasType Γ _ [A, B]) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationSoundness.denote_dispatch_bind J M ha

end Soundness

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare
