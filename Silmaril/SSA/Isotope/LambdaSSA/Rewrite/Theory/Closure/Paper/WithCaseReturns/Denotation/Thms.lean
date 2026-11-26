module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseUnaryReturnDenotation

/-! # Model soundness for case returns and unary forwarding fusion -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (SeedDenotes)

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

include shared

/-- The two extra steps of the acyclic round-trip quotient have common
denotations. The shared tensor comparison at `(E, E)` gives the needed
centrality of the interpreted diagonal. -/
theorem caseUnary_seedDenotes : SeedDenotes (Φ := Φ) (Seed := CaseUnary) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseUnaryReturnDenotation.caseUnaryDenotes J M shared pe

/-- With the same model hypotheses, include projection returns and unit η
from the existing case-return join as well as unary fusion. -/
theorem joinedUnary_seedDenotes : SeedDenotes (Φ := Φ) (Seed := JoinedUnary) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseUnaryReturnDenotation.joinedUnaryDenotes J M shared pe

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns
