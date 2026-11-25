module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.DirectSubstitution

/-! # Direct categorical label substitution without local iteration -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "fst" => CartesianMonoidalCategory.fst

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Under a fresh captured value, the continuation ignores that value and
still receives its label argument. This transports bodies with local CFGs. -/
theorem ContinuationDenotes.weakenCapture {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) (B : τ) :
    ContinuationDenotes J M (Γ := B :: Γ) (Region.liftLSubstVars σ)
      (J.map (fst (ctxObj M Γ) (M.obj B) ▷ labelObj M L) ≫ k) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.continuation_weakenCapture J M d B

/-- Direct substitution into a single pure branch denotes sequencing its
payload into the corresponding continuation. The continuation can use effects
and arbitrary local control flow. -/
theorem RegionDenotes.branch_lsubst {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k)
    {a : Tm Φ} {A : τ} {ha : Tm.HasType Γ a A} {p : ctxObj M Γ ⟶ M.obj A}
    (da : Denotes J M ha (J.map p)) {i : Nat} (h : At L i A) :
    ∃ ht : Region.HasType Γ ((Region.br i a).lsubst σ) K,
      RegionDenotes J M ht (bindArrow J (J.map p ≫ J.map (labelInject M i h)) k) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.regionDenotes_branch_lsubst J M d da h

variable (copyCentral : ∀ E : V, IsCentral (J.map (duplicate E) ≫
  (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
include copyCentral

/-- The structural equation of Theorem 5.12(a) for regions without local
blocks. The transported Cartesian diagonals commute with effects. -/
theorem RegionDenotes.lsubst_noLocalBlocks {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (values : Region.ValueBranches Γ r L) (noBlocks : r.NoLocalBlocks) {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) :
    ∃ (hr : Region.HasType Γ r L) (ht : Region.HasType Γ (r.lsubst σ) K), ∃ f,
      RegionDenotes J M hr f ∧ RegionDenotes J M ht (bindArrow J f k) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.noLocalBlocks_lsubst J M copyCentral values noBlocks d

variable [RegionTypingCoherent (Φ := Φ) J M]

/-- Theorem 5.12(a) for the chosen arrows in the same fragment. -/
theorem denoteRegion_lsubst_noLocalBlocks {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (ht : Region.HasType Γ (r.lsubst σ) K)
    (values : Region.ValueBranches Γ r L) (noBlocks : r.NoLocalBlocks)
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) :
    denoteRegion J M ht = bindArrow J (denoteRegion J M hr) k := by
  obtain ⟨_, _, _, df, dt⟩ := RegionDenotes.lsubst_noLocalBlocks J M copyCentral values noBlocks d
  rw [← RegionDenotes.eq_denote (h := ht) J M dt, RegionDenotes.eq_denote (h := hr) J M df]

/-- Theorem 5.12(b) when the first family has constructor-valued branches
and no local blocks. The second family can have arbitrary typed bodies. -/
theorem ContinuationDenotes.compose_noLocalBlocks {Γ : VCtx τ} {L K H : LCtx τ}
    {σ υ : Nat → Region Φ}
    {first : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    {after : J.obj (ctxObj M Γ ⊗ labelObj M K) ⟶ J.obj (labelObj M H)}
    (dFirst : ContinuationDenotes J M σ first) (dAfter : ContinuationDenotes J M υ after)
    (values : ∀ ⦃i A⦄, At L i A → Region.ValueBranches (A :: Γ) (σ i) K)
    (noBlocks : ∀ ⦃i A⦄, At L i A → (σ i).NoLocalBlocks) :
    ContinuationDenotes J M (Region.compLSubst σ υ)
      (composeContinuations J M (Γ := Γ) (L := L) (K := K) (H := H) first after) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.composeContinuations_noLocalBlocks J M copyCentral dFirst dAfter
    values noBlocks

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
