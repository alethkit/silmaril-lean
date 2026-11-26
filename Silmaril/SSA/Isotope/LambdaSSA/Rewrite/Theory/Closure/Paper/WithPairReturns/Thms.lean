module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnGeneration

/-! # The generated pair arrow and model soundness -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (ofRegion pairArrows SeedDenotes)
open Paper.Extension.Singleton.Generation (Generated)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {ε : Type w} [HasEff Φ ε]

section Generation

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includePair : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
  (includeUnary : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Paper.UnaryReturn.Step Γ r s L → Seed Γ r s L)
  {X A B : τ} {a b : Tm Φ}

set_option hygiene false in
local notation "Lit" => ofRegion Seed

include includePair includeUnary in
/-- Returning a pair agrees with the existing left-to-right singleton pairing. -/
theorem returnPair_eq_pairArrows (ha : Tm.HasType [X] a A) (hb : Tm.HasType [X] b B) :
    Lit (returnRegion_typed (.pair ha hb)) =
      pairArrows Seed (Lit (returnRegion_typed ha)) (Lit (returnRegion_typed hb)) :=
  PairReturnGeneration.returnPair_eq_pairArrows Seed includePair includeUnary ha hb

include includePair includeUnary in
/-- The return of a pair is generated when both of its returned operands are generated. -/
theorem generated_returnPair (ha : Tm.HasType [X] a A) (hb : Tm.HasType [X] b B)
    (ga : Generated Seed (Lit (returnRegion_typed ha))) (gb : Generated Seed (Lit (returnRegion_typed hb))) :
    Generated Seed (Lit (returnRegion_typed (.pair ha hb))) :=
  PairReturnGeneration.generated_returnPair Seed includePair includeUnary ha hb ga gb

end Generation

section Soundness

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The pair step has the same denotation at both endpoints for any exact typing. -/
theorem step_denotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M :=
  PairReturnGeneration.step_denotes J M

/-- The joined seed has common denotations in the coherent shared-tensor model. -/
theorem joined_seedDenotes
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    (pe : ε) : SeedDenotes (Seed := JoinedStep (τ := τ) (Φ := Φ) pe) J M :=
  PairReturnGeneration.joined_seedDenotes J M shared pe

end Soundness

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns
