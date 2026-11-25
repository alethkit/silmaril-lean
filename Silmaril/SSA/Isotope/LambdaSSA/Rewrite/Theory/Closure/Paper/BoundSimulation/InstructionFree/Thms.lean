module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InstructionFreeSimulation

/-! # Soundness of standalone instruction-free bound simulation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem InstructionFreeStep.valueBranches {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : InstructionFreeStep Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InstructionFreeSimulation.valueBranches e

theorem InstructionFreeStep.typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : InstructionFreeStep Γ r s L) : HasType Γ r L ∧ HasType Γ s L :=
  ⟨e.valueBranches.1.hasType, e.valueBranches.2.hasType⟩

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- Both typed endpoints denote the same arrow under the existing Paper model
hypotheses, including equality-induced tensor comparisons. No condition on
primitive interpretations is needed for an instruction-free state change. -/
theorem InstructionFreeStep.denotes
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : InstructionFreeStep Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InstructionFreeSimulation.denotes J M shared e hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
