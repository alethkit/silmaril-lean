module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionDenotation

/-! # Denotation on a singleton quotient with sound extra equations -/

@[expose] public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

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

variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

/-- Each extra equation has one denotation at both exact endpoint typings. -/
abbrev SeedDenotes : Prop :=
  ∀ {Γ r s L}, Seed Γ r s L → ∀ (hr : HasType Γ r L) (hs : HasType Γ s L),
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f

/-- Descend the guarded denotation functor along the contextual quotient. -/
noncomputable def denoteFunctor (sound : SeedDenotes (Seed := Seed) J M) :
    TypeCategory Seed ⥤ C :=
  CategoryTheory.Quotient.lift (homRel Seed) (Paper.TypeCategory.denoteFunctor J M shared)
    (by
      intro _ _ _ _ h
      exact Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionDenotation.homRel_denoteArrow
        J M shared sound h)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
