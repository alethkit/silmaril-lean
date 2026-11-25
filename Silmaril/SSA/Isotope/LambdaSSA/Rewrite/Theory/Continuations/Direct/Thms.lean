module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Purity.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.DirectSubstitution

/-! # Direct categorical label substitution in strong Elgot Freyd models -/

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

/-- Constructor-valued arguments give pure branch denotations. -/
theorem PureBranches.of_valueBranches {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (values : Region.ValueBranches Γ r L) : PureBranches J M Γ r L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.pureBranches_of_values J M values

/-- A typed pure expression gives the branch premise when its pure
instructions are interpreted by value arrows. -/
theorem PureBranches.br_of_pure {ε : Type*} [HasEff Φ ε] {pureEff : ε}
    (hInstr : ∀ f : Φ, IsPure pureEff f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {A : τ} {i : Nat}
    (h : At L i A) (ha : Tm.HasType Γ a A) (hp : a.Pure pureEff) :
    PureBranches J M Γ (.br i a) L := by
  obtain ⟨_, da⟩ := hp.denotes_map J M ha hInstr
  exact .br h da

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

omit copyCentral
variable [FreydCategory.CentralUnit J]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include shared

omit [RegionTypingCoherent (Φ := Φ) J M] in
/-- Theorem 5.12(a) in the structural denotation graph, including nested CFGs.
The tensor comparison is the identity under the shared tensor objects. -/
theorem RegionDenotes.lsubst_sharedTensor {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (values : PureBranches J M Γ r L) {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) :
    ∃ (hr : Region.HasType Γ r L) (ht : Region.HasType Γ (r.lsubst σ) K), ∃ f,
      RegionDenotes J M hr f ∧ RegionDenotes J M ht (bindArrow J f k) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.lsubst_sharedTensor J M shared values d

/-- Theorem 5.12(a) for the chosen arrows and any well-typed continuation in
a coherent model with shared tensor comparisons. -/
theorem denoteRegion_lsubst_sharedTensor {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (ht : Region.HasType Γ (r.lsubst σ) K)
    (values : PureBranches J M Γ r L)
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) :
    denoteRegion J M ht = bindArrow J (denoteRegion J M hr) k := by
  obtain ⟨_, _, _, df, dt⟩ := RegionDenotes.lsubst_sharedTensor J M shared values d
  rw [← RegionDenotes.eq_denote (h := ht) J M dt, RegionDenotes.eq_denote (h := hr) J M df]

/-- Theorem 5.12(b) with shared tensor comparisons. The first family has
pure branch arguments and can contain arbitrary local CFGs. -/
theorem ContinuationDenotes.compose_sharedTensor {Γ : VCtx τ} {L K H : LCtx τ}
    {σ υ : Nat → Region Φ}
    {first : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    {after : J.obj (ctxObj M Γ ⊗ labelObj M K) ⟶ J.obj (labelObj M H)}
    (dFirst : ContinuationDenotes J M σ first) (dAfter : ContinuationDenotes J M υ after)
    (values : ∀ ⦃i A⦄, At L i A → PureBranches J M (A :: Γ) (σ i) K) :
    ContinuationDenotes J M (Region.compLSubst σ υ)
      (composeContinuations J M (Γ := Γ) (L := L) (K := K) (H := H) first after) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.composeContinuations_sharedTensor J M shared dFirst dAfter values

/-- Binding each argument once before substitution gives the categorical
sequencing equation for arbitrary exactly typed source regions. -/
theorem denoteRegion_bound_lsubst_sharedTensor {Γ : VCtx τ} {L K : LCtx τ}
    {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L)
    (ht : Region.HasType Γ (r.bindBranchArguments.lsubst σ) K)
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) :
    denoteRegion J M ht = bindArrow J (denoteRegion J M hr) k := by
  rw [denoteRegion_lsubst_sharedTensor J M shared hr.bindBranchArguments.hasType ht
    (PureBranches.of_valueBranches J M hr.bindBranchArguments) d,
    ← Region.denoteRegion_bindBranchArguments J M (FreydCategory.CentralUnit.unit_central (J := J)) hr]

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
