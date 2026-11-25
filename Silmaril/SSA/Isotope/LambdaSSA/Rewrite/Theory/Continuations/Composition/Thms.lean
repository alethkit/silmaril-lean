module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Composition.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LinkedComposition
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LinkedCongruence

/-! # Native congruence and categorical interpretation of linked composition -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA

section Syntax

variable {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]

/-- The linked CFG respects exact types and the native equations on its
entry and all continuation bodies. -/
theorem Region.SubstitutionEquiv.linkExits {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : Region.SubstitutionEquiv Γ r s L) {σ υ : Nat → Region Φ}
    (hσ : ∀ ⦃i A⦄, At L i A → Region.SubstitutionEquiv (A :: Γ) (σ i) (υ i) K) :
    Region.SubstitutionEquiv Γ (r.linkExits L σ) (s.linkExits L υ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.substitutionEquiv_linkExits h hσ

theorem Region.linkCompLSubst_hasType {Γ : VCtx τ} {L K H : LCtx τ}
    {σ υ : Nat → Region Φ} (hσ : Region.LSubst.HasType Γ L K σ) (hυ : Region.LSubst.HasType Γ K H υ) :
    Region.LSubst.HasType Γ L H (Region.linkCompLSubst K σ υ) :=
  fun _ A h => (hσ h).linkExits (hυ.liftVars A)

/-- Linking composes continuation families up to their native rewrite classes. -/
theorem Region.linkCompLSubst_congr {Γ : VCtx τ} {L K H : LCtx τ} {σ σ' υ υ' : Nat → Region Φ}
    (hσ : ∀ ⦃i A⦄, At L i A → Region.SubstitutionEquiv (A :: Γ) (σ i) (σ' i) K)
    (hυ : ∀ ⦃i A⦄, At K i A → Region.SubstitutionEquiv (A :: Γ) (υ i) (υ' i) H) :
    ∀ ⦃i A⦄, At L i A →
      Region.SubstitutionEquiv (A :: Γ) (Region.linkCompLSubst K σ υ i)
        (Region.linkCompLSubst K σ' υ' i) H :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.linkCompLSubst_congr hσ hυ

end Syntax

namespace Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

variable [FreydCategory.CentralUnit J]

/-- Categorical continuation composition denotes the linked CFG family.
Both families may run effects, contain loops, and read their common captures. -/
theorem ContinuationDenotes.linkComp {Γ : VCtx τ} {L K H : LCtx τ}
    {σ υ : Nat → Region Φ}
    {first : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    {after : J.obj (ctxObj M Γ ⊗ labelObj M K) ⟶ J.obj (labelObj M H)}
    (df : ContinuationDenotes J M σ first) (dg : ContinuationDenotes J M υ after) :
    ContinuationDenotes J M (Region.linkCompLSubst K σ υ)
      (composeContinuations J M (Γ := Γ) (L := L) (K := K) (H := H) first after) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.continuationDenotes_linkComp J M df dg

end Semantics.Categorical
end Silmaril.Isotope.LambdaSSA
