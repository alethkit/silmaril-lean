module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.Soundness

/-! # Constructor sequencing and contextual soundness -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing

open Silmaril Silmaril.Isotope.LambdaSSA
open UnaryReturn.Beta.Constructors
open RetainedLet (returnOnce)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} {a c : Tm Φ} {A : τ}

theorem Step.valueBranches (e : Step Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.step_valueBranches e

theorem Step.eqv (e : Step Γ r s L) : Eqv Γ r s L :=
  .extra e.valueBranches.1.hasType e.valueBranches.2.hasType (.inr e)

/-- The three singleton steps discharge the mixed normalization premises. -/
theorem constructorSequencing : ConstructorSequencing (Seed (τ := τ) (Φ := Φ)) where
  pair ha hb := (Step.pair ha hb).eqv
  inl ha := (Step.inl ha).eqv
  inr ha := (Step.inr ha).eqv

theorem returnOnce_eq_branch (h : Normalizes Γ a c A) :
    Eqv Γ (returnOnce a) (.br 0 c) [A] :=
  h.returnOnce_eq_branch (fun e => .inl e) constructorSequencing

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The constructor root steps preserve denotation at their exact interfaces. -/
theorem Step.sound (e : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.step_sound J M e hr hs

/-- Soundness of the contextual closure under the existing Paper model hypotheses. -/
theorem Eqv.sound
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (e : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Extension.Eqv.sound J M shared (fun seed hp hq =>
    seed.elim (fun h => h.denotes J M hp hq)
      (fun h => ⟨_, denoteRegion_spec J M hp, (h.sound J M hp hq).symm ▸ denoteRegion_spec J M hq⟩))
    e hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing
