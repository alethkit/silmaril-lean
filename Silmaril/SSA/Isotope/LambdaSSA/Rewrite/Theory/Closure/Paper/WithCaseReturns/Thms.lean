module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseReturns

/-! # Value coproducts and soundness of the case-return extension -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open scoped MonoidalCategory
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts (CopairPure)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- A contextual seed containing the case-return equation has pure copairs. -/
theorem copairPure_of_includesCaseReturn
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (includeCase : ∀ {Γ r s L}, Step pe Γ r s L → Seed Γ r s L) :
    CopairPure Seed pe :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseReturns.copairPure_of_includesCaseReturn pe Seed includeCase

/-- The joined case-return quotient has pure copairs. -/
theorem copairPure : CopairPure (JoinedStep (τ := τ) (Φ := Φ) pe) pe :=
  copairPure_of_includesCaseReturn pe _ Or.inr

instance hasFiniteCoproducts : HasFiniteCoproducts (ValueCategory (τ := τ) (Φ := Φ) pe) :=
  Extension.Singleton.ValueCoproducts.valueHasFiniteCoproducts (JoinedStep pe) pe (copairPure pe)

instance preservesFiniteCoproducts : PreservesFiniteCoproducts (values (τ := τ) (Φ := Φ) pe) :=
  Extension.Singleton.ValueCoproducts.valuePreservesFiniteCoproducts (JoinedStep pe) pe (copairPure pe)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The single case-return step denotes the same arrow at both endpoints. -/
theorem Step.sound
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Step pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  WithCaseReturns.step_sound pe J M copyCentral e hr hs

/-- The contextual join is sound under the existing Paper hypotheses with shared tensor. -/
theorem Eqv.sound
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  WithCaseReturns.eqv_sound pe J M shared e hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns
