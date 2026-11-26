module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallReturns

/-! # Generation and coherent denotation with computed primitive operands -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (ofRegion SeedDenotes)
open Paper.Extension.Singleton.Generation (Generated)
open Paper.WithPairReturns (CallReturnAgreement ReturnFragmentWithCalls generated_returnFragment_of)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Join" => JoinedStep (τ := τ) (Φ := Φ) pe

/-- The added call equation holds for every typed operand at its single exit. -/
theorem callReturnAgreement : CallReturnAgreement Join :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallReturns.callReturnAgreement pe

/-- The same return induction now admits recursively generated call operands. -/
theorem generated_returnFragment {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragmentWithCalls pe true ht) : Generated Join (ofRegion Join (returnRegion_typed ht)) :=
  generated_returnFragment_of pe Join Or.inl (fun _ => callReturnAgreement pe) h

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include shared in
/-- The new generator has a common denotation at both exact typings. -/
theorem step_denotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallReturns.step_denotes J M shared

include shared in
/-- The existing coherent model interface interprets the enlarged quotient. -/
theorem joined_seedDenotes : SeedDenotes (Seed := Join) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallReturns.joined_seedDenotes pe J M shared

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns
