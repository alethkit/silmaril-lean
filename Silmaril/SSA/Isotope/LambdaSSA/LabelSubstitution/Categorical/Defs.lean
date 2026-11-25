module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

/-! # Categorical continuation denotation -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- On each label summand the supplied arrow denotes the corresponding
replacement, with the same captured environment. -/
def ContinuationDenotes {Γ : VCtx τ} {L K : LCtx τ} (σ : Nat → Region Φ)
    (k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)) : Prop :=
  ∀ ⦃i A⦄ (h : At L i A), ∃ d : Region.HasType (A :: Γ) (σ i) K,
    RegionDenotes J M d (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelInject M i h) ≫ k)

/-- Compose two continuation arrows while retaining the captured values.
The first label argument is discarded after the first arrow runs. -/
noncomputable def composeContinuations {Γ : VCtx τ} {L K H : LCtx τ}
    (first : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K))
    (after : J.obj (ctxObj M Γ ⊗ labelObj M K) ⟶ J.obj (labelObj M H)) :
    J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M H) :=
  bind J first
    (J.map (CartesianMonoidalCategory.fst (ctxObj M Γ) (labelObj M L) ⊗ₘ 𝟙 (labelObj M K)) ≫ after)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
