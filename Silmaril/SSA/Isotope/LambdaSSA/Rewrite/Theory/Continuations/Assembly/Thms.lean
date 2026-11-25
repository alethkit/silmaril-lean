module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationAssembly

/-! # Assemble a categorical arrow for a typed continuation family -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]
  {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ]

/-- A typed continuation family has one arrow restricting to the denotation
of each body at its corresponding label. -/
theorem ContinuationDenotes.exists_of_typed {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : Region.LSubst.HasType Γ L K σ) :
    ∃ k, ContinuationDenotes J M (Γ := Γ) (L := L) (K := K) σ k :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationAssembly.ofTyped M J hσ

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
