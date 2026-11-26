module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Soundness.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseUnaryReturnDenotation

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

open Paper.Extension.Singleton (SeedDenotes)

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

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "CaseUnary" =>
  (fun Γ r s L => Paper.UnaryReturn.Step Γ r s L ∨ Paper.WithCaseReturns.Step pe Γ r s L)
local notation "JoinedUnary" =>
  (fun Γ r s L => Paper.WithCaseReturns.JoinedStep pe Γ r s L ∨ Paper.UnaryReturn.Step Γ r s L)

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)

include shared

private theorem caseDenotes :
    SeedDenotes (Φ := Φ) (Seed := Paper.WithCaseReturns.Step pe) J M := by
  intro Γ r s L e hr hs
  have copyCentral (E : V) : PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv) := by
    obtain ⟨h, hE⟩ := shared E E
    exact Silmaril.Isotope.LetIter.Semantics.Categorical.duplicate_central_of_tensor_eqToIso J E h hE
  have he := Paper.WithCaseReturns.Step.sound pe J M copyCentral e hr hs
  exact ⟨_, denoteRegion_spec J M hr, he.symm ▸ denoteRegion_spec J M hs⟩

theorem caseUnaryDenotes : SeedDenotes (Φ := Φ) (Seed := CaseUnary) J M := by
  intro Γ r s L e hr hs
  exact e.elim (fun h => Paper.UnaryReturn.Step.denotes J M h hr hs)
    (fun h => caseDenotes J M shared pe h hr hs)

theorem joinedUnaryDenotes : SeedDenotes (Φ := Φ) (Seed := JoinedUnary) J M := by
  intro Γ r s L e hr hs
  rcases e with (e | e) | e
  · exact Paper.WithProjectionReturnsAndUnitEta.step_denotes J M e hr hs
  · exact caseDenotes J M shared pe e hr hs
  · exact Paper.UnaryReturn.Step.denotes J M e hr hs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseUnaryReturnDenotation
