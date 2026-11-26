module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold

/-! # Binary-fold soundness and arbitrary-state alternating iteration -/

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold

open Paper.BoundSimulation

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

variable {Γ : VCtx τ} {L : LCtx τ} {A D : τ}

/-- Both endpoints retain their exact guarded branch interfaces. -/
theorem FoldStep.valueBranches {r s : Region Φ} (e : FoldStep pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold.foldStep_valueBranches pe e

/-- The existing case-return relation embeds into the binary-fold extension. -/
theorem old_case_returns_included {r s : Region Φ}
    (h : Paper.WithCaseReturns.Eqv pe Γ r s L) :
    Paper.Extension.Eqv (JoinedStep pe) Γ r s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold.old_case_returns_included pe h

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The fold step has a common structural denotation in every shared-tensor Paper model. -/
theorem FoldStep.denotes
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {r s : Region Φ} (e : FoldStep pe Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold.foldStep_denotes pe J M shared e hr hs

/-- Contextual binary-fold equations preserve the chosen denotation. -/
theorem Eqv.sound
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {r s : Region Φ} (eq : Eqv pe Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold.fold_extra_preserves_denotation pe J M shared eq hr hs

section Alternating

open Paper.TypeCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (iterateChosen)

local notation "Q" => TypeCategory (τ := τ) (Φ := Φ) pe
local notation "E" => JoinedStep (τ := τ) (Φ := Φ) pe
variable {B : τ} {p q : Region Φ}
local notation "T" => Silmaril.coprod A A

/-- The two alternating rows satisfy the seed premise in the original case-return relation. -/
theorem local_square (hp : ValueBranches [T] p [T, B])
    (hq : ValueBranches [A] q [A, B])
    (comm : stepArrow hp = alternatingStep (stepArrow hq)) :
    Paper.WithCaseReturns.Eqv pe [T] (p.lsubst (liftLSubstVars (boundLocalMap foldTerm)))
      ((Region.br 0 foldTerm).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) [A, B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold.local_square pe hp hq comm

/-- Two consecutive steps have the same iteration as one step in the binary-fold quotient. -/
theorem double_step {A B : Q} (g : A ⟶ B ⨿ A) :
    iterateChosen E (g ≫ coprod.desc coprod.inl g) = iterateChosen E g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold.double_step pe g

end Alternating

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold
