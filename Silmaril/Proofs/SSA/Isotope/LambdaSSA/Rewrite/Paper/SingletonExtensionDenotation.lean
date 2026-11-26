module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Defs

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionDenotation

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton (homRel)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include shared

theorem homRel_denoteArrow {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (seedDenotes : ∀ {Γ r s L}, Seed Γ r s L →
      ∀ (hr : HasType Γ r L) (hs : HasType Γ s L),
        ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f)
    {A B : Paper.TypeCategory (τ := τ) Φ} {f g : A ⟶ B} (h : homRel Seed f g) :
    Paper.TypeCategory.denoteArrow J M f = Paper.TypeCategory.denoteArrow J M g := by
  obtain ⟨_, _, hr, hs, rfl, rfl, eq⟩ := h
  rw [Paper.TypeCategory.denoteArrow_ofRegion J M shared,
    Paper.TypeCategory.denoteArrow_ofRegion J M shared]
  unfold denoteSingletonRegion
  rw [Paper.Extension.Eqv.sound J M shared seedDenotes eq hr.hasType hs.hasType]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionDenotation
