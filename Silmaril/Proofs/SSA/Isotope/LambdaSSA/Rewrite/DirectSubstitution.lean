module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Soundness.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationBind
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution

/-! # Direct label substitution in the categorical denotation graph -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext duplicate extend)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "fst" => CartesianMonoidalCategory.fst
local notation "lift" => CartesianMonoidalCategory.lift

set_option backward.isDefEq.respectTransparency false

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

theorem continuation_weakenCapture {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) (B : τ) :
    ContinuationDenotes J M (Γ := B :: Γ) (Region.liftLSubstVars σ)
      (J.map (fst (ctxObj M Γ) (M.obj B) ▷ labelObj M L) ≫ k) := by
  intro i A h
  obtain ⟨ht, dt⟩ := d h
  refine ⟨ht.renameVars ((Ren.wk Γ B).lift A), ?_⟩
  have dw := regionDenotes_weakenCapture_proof J M B dt
  simp only [MonoidalCategory.id_tensorHom] at dw ⊢
  rw [← J.map_comp_assoc, MonoidalCategory.whisker_exchange, J.map_comp_assoc]
  exact dw

theorem regionDenotes_branch_lsubst {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k)
    {a : Tm Φ} {A : τ} {ha : Tm.HasType Γ a A} {p : ctxObj M Γ ⟶ M.obj A}
    (da : Denotes J M ha (J.map p)) {i : Nat} (h : At L i A) :
    ∃ ht : Region.HasType Γ ((Region.br i a).lsubst σ) K,
      RegionDenotes J M ht (bindArrow J (J.map p ≫ J.map (labelInject M i h)) k) := by
  obtain ⟨_, dc⟩ := d h
  obtain ⟨ht, dt⟩ := dc.substValue J M da
  refine ⟨ht, ?_⟩
  have pipe : lift (𝟙 (ctxObj M Γ)) (p ≫ labelInject M i h) =
      lift (𝟙 (ctxObj M Γ)) p ≫ (ctxObj M Γ ◁ labelInject M i h) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change RegionDenotes J M ht (extend J (J.map p ≫ J.map (labelInject M i h)) ≫ k)
  rw [← J.map_comp, extend_map, pipe, J.map_comp_assoc]
  simpa only [MonoidalCategory.id_tensorHom, Category.assoc] using dt

theorem composeContinuations_restrict {Γ : VCtx τ} {L K H : LCtx τ}
    (first : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K))
    (after : J.obj (ctxObj M Γ ⊗ labelObj M K) ⟶ J.obj (labelObj M H))
    {i : Nat} {A : τ} (h : At L i A) :
    J.map (ctxObj M Γ ◁ labelInject M i h) ≫
        composeContinuations J M (Γ := Γ) (L := L) (K := K) (H := H) first after =
      bindArrow J (J.map (ctxObj M Γ ◁ labelInject M i h) ≫ first)
        (J.map (fst (ctxObj M Γ) (M.obj A) ▷ labelObj M K) ≫ after) := by
  let inj := ctxObj M Γ ◁ labelInject M i h
  have proj : (inj ▷ labelObj M K) ≫
      (fst (ctxObj M Γ) (labelObj M L) ▷ labelObj M K) =
      fst (ctxObj M Γ) (M.obj A) ▷ labelObj M K := by
    rw [← MonoidalCategory.comp_whiskerRight, CartesianMonoidalCategory.whiskerLeft_fst]
  simp only [composeContinuations, MonoidalCategory.tensorHom_id]
  rw [← bind_pre_map, ← J.map_comp_assoc, proj]

theorem noLocalBlocks_lsubst
    (copyCentral : ∀ E : V, IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (values : Region.ValueBranches Γ r L) (noBlocks : r.NoLocalBlocks) {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) :
    ∃ (hr : Region.HasType Γ r L) (ht : Region.HasType Γ (r.lsubst σ) K), ∃ f,
      RegionDenotes J M hr f ∧ RegionDenotes J M ht (bindArrow J f k) := by
  induction values generalizing K σ with
  | br h ha =>
    obtain ⟨_, da⟩ := ha.denotes_map J M
    obtain ⟨ht, dt⟩ := regionDenotes_branch_lsubst J M d da h
    exact ⟨_, ht, _, .br da, dt⟩
  | let₁ ha _ ih =>
    obtain ⟨hr, ht, _, dr, dt⟩ := ih noBlocks (continuation_weakenCapture J M d _)
    let da := denote_spec J M ha
    refine ⟨.let₁ ha hr, .let₁ ha ht, _, .let₁ da dr, ?_⟩
    rw [bind_assoc_capture J (copyCentral _)]
    exact .let₁ da dt
  | let₂ ha _ ih =>
    obtain ⟨hr, ht, _, dr, dt⟩ := ih noBlocks
      (continuation_weakenCapture J M (continuation_weakenCapture J M d _) _)
    let da := denote_spec J M ha
    refine ⟨.let₂ ha hr, .let₂ ha ht, _, .let₂ da dr, ?_⟩
    have fstPair (E P A B : V) (unpack : P ⟶ A ⊗ B) :
        ((E ◁ unpack) ≫ (α_ E A B).inv) ≫ (fst (E ⊗ A) B ≫ fst E A) = fst E P := by
      simp only [Category.assoc]
      rw [← CartesianMonoidalCategory.associator_hom_fst, Iso.inv_hom_id_assoc,
        CartesianMonoidalCategory.whiskerLeft_fst]
    simp only [MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom, ← J.map_comp_assoc]
    rw [bind_assoc_reindex J (copyCentral _) _ _ _ _ (fstPair _ _ _ _ _)]
    simp only [J.map_comp_assoc, MonoidalCategory.comp_whiskerRight]
    simpa only [Region.lsubst, ctxObj, MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom] using RegionDenotes.let₂ da dt
  | case ha _ _ ihl ihr =>
    obtain ⟨hl, hlt, _, dl, dlt⟩ := ihl noBlocks.1 (continuation_weakenCapture J M d _)
    obtain ⟨hr, hrt, _, dr, drt⟩ := ihr noBlocks.2 (continuation_weakenCapture J M d _)
    let da := denote_spec J M ha
    refine ⟨.case ha hl hr, .case ha hlt hrt, _, .case da dl dr, ?_⟩
    rw [bind_case_capture J (copyCentral _)]
    exact .case da dlt drt
  | cfg R _ _ ihe _ =>
    obtain ⟨hn, he⟩ := noBlocks
    subst hn
    obtain ⟨hr, ht, _, dr, dt⟩ := ihe he d
    exact ⟨.cfg R hr (fun i => i.elim0), .cfg R ht (fun i => i.elim0), _,
      .cfgZero (R := R) hr (fun i => i.elim0) dr, .cfgZero (R := R) (L := K) ht (fun i => i.elim0) dt⟩

theorem composeContinuations_noLocalBlocks
    (copyCentral : ∀ E : V, IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {L K H : LCtx τ} {σ υ : Nat → Region Φ}
    {first : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    {after : J.obj (ctxObj M Γ ⊗ labelObj M K) ⟶ J.obj (labelObj M H)}
    (dFirst : ContinuationDenotes J M σ first) (dAfter : ContinuationDenotes J M υ after)
    (values : ∀ ⦃i A⦄, At L i A → Region.ValueBranches (A :: Γ) (σ i) K)
    (noBlocks : ∀ ⦃i A⦄, At L i A → (σ i).NoLocalBlocks) :
    ContinuationDenotes J M (Region.compLSubst σ υ)
      (composeContinuations J M (Γ := Γ) (L := L) (K := K) (H := H) first after) := by
  intro i A h
  obtain ⟨hr, df⟩ := dFirst h
  obtain ⟨_, ht, _, ds, dt⟩ := noLocalBlocks_lsubst J M copyCentral (values h) (noBlocks h)
    (continuation_weakenCapture J M dAfter A)
  have eq := RegionTypingCoherent.denotes_eq (h := hr) ds df
  refine ⟨ht, ?_⟩
  rw [MonoidalCategory.id_tensorHom, composeContinuations_restrict]
  simp only [MonoidalCategory.id_tensorHom] at eq
  exact eq ▸ dt

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
