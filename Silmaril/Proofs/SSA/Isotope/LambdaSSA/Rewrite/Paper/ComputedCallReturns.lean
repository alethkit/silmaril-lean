module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Generated calls and soundness of the opt-in equation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedCallReturns
open Paper.Extension.Singleton (ofRegion SeedDenotes)
open Paper.Extension.Singleton.Generation (Generated)
open CfgEta.TypeCategory (returnRegion_typed)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel duplicate_central_of_tensor_eqToIso)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

theorem callReturnAgreement : Paper.WithPairReturns.CallReturnAgreement (JoinedStep (τ := τ) (Φ := Φ) pe) := by
  intro Γ a p ha
  let h := Step.seq p ha
  exact .extra h.valueBranches.1.hasType h.valueBranches.2.hasType (.inr h)

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include shared in
theorem step_denotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M := by
  intro Γ r s L h hr hs
  cases h with
  | seq p ha =>
    have eq := denote_op_returnRegion_sequencing J M (fun E => by
      obtain ⟨e, he⟩ := shared E E
      exact duplicate_central_of_tensor_eqToIso J E e he) p ha
    exact ⟨_, denoteRegion_spec J M hr, eq.symm ▸ denoteRegion_spec J M hs⟩

include shared in
theorem joined_seedDenotes : SeedDenotes (Seed := JoinedStep (τ := τ) (Φ := Φ) pe) J M := by
  intro Γ r s L h hr hs
  exact h.elim (fun old => Paper.WithPairReturns.joined_seedDenotes J M shared pe old hr hs)
    (fun step => step_denotes J M shared step hr hs)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallReturns
