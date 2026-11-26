module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Renaming.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

/-! # Read the state factorization from typed row witnesses -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel case_pre_map case_postcomp)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

section Labels

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty κ) V) {n : Nat} (R : Fin n → Ty κ)

local notation "Small" => labelObj M (List.ofFn R)
local notation "Wide" D => family R (some D)
local notation "Big" D => labelObj M (List.ofFn (Wide D))

private noncomputable abbrev tag (D : Fin n → Ty κ) (i : Fin n) :
    M.obj (R i) ⟶ M.obj ((Wide D) i) :=
  coprod.inl ≫ (M.coprodIso (R i) (D i)).inv

local notation "embedding" => embedLabels

private noncomputable def finiteEmbedding (D : Fin n → Ty κ) :
    finiteLabelObj M R ⟶ finiteLabelObj M (Wide D) :=
  Sigma.desc fun i => tag M R D i ≫ finiteLabelInject M (Wide D) i

@[reassoc] private theorem label_embed (D : Fin n → Ty κ) (i : Fin n) :
    labelInject M i (local_label R i) ≫ embedding M R D =
      tag M R D i ≫ labelInject M i (local_label (Wide D) i) := by
  unfold embedLabels
  erw [← Category.assoc, labelObjToFinite_local M R i (local_label R i)]
  exact Sigma.ι_comp_desc _ _

@[reassoc] private theorem finite_embed (D : Fin n → Ty κ) (i : Fin n) :
    finiteLabelInject M R i ≫ finiteEmbedding M R D = tag M R D i ≫ finiteLabelInject M (Wide D) i :=
  Sigma.ι_comp_desc _ _

private theorem embedding_toFinite (D : Fin n → Ty κ) :
    embedding M R D ≫ labelObjToFinite M (Wide D) =
      labelObjToFinite M R ≫ finiteEmbedding M R D := by
  unfold embedLabels
  erw [Category.assoc]
  congr 1
  apply Sigma.hom_ext
  intro i
  change finiteLabelInject M R i ≫ _ = finiteLabelInject M R i ≫ _
  erw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, labelObjToFinite_local, finite_embed]

private noncomputable def labelChange (tails : Option (Fin n → Ty κ)) :
    Small ⟶ labelObj M (List.ofFn (family R tails)) :=
  match tails with
  | none => 𝟙 _
  | some D => embedding M R D

private noncomputable def payloadChange (tails : Option (Fin n → Ty κ)) (i : Fin n) :
    M.obj (R i) ⟶ M.obj (family R tails i) :=
  match tails with
  | none => 𝟙 _
  | some D => tag M R D i

private noncomputable def finiteChange (tails : Option (Fin n → Ty κ)) :
    finiteLabelObj M R ⟶ finiteLabelObj M (family R tails) :=
  match tails with
  | none => 𝟙 _
  | some D => finiteEmbedding M R D

private theorem finite_change_inject (tails : Option (Fin n → Ty κ)) (i : Fin n) :
    finiteLabelInject M R i ≫ finiteChange M R tails =
      payloadChange M R tails i ≫ finiteLabelInject M (family R tails) i := by
  cases tails with
  | none => simp only [family, finiteChange, payloadChange, Category.comp_id, Category.id_comp]
  | some D => exact finite_embed M R D i

private theorem change_toFinite (tails : Option (Fin n → Ty κ)) :
    labelChange M R tails ≫ labelObjToFinite M (family R tails) =
      labelObjToFinite M R ≫ finiteChange M R tails := by
  cases tails with
  | none => simp only [family, labelChange, finiteChange, Category.comp_id, Category.id_comp]
  | some D => exact embedding_toFinite M R D

end Labels

section Graph

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty κ) V) [InstructionModel J M Φ]

variable {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)}

local notation "Small" => labelObj M (List.ofFn R)
local notation "ExitObj" => labelObj M L

private noncomputable def eval {Γ : VCtx (Ty κ)} :
    Row (Φ := Φ) R L Γ → (J.obj (ctxObj M Γ) ⟶ J.obj (ExitObj ⨿ Small))
  | .jump i arg => denote J M (operand_base arg) ≫
      J.map (labelInject M i (local_label R i) ≫ coprod.inr)
  | .exit i hit arg => denote J M (operand_base arg) ≫ J.map (labelInject M i hit ≫ coprod.inl)
  | .case arg left right => caseWithContext J
      (denote J M (operand_base arg) ≫ J.map (M.coprodIso _ _).hom)
      (eval left) (eval right)

set_option backward.isDefEq.respectTransparency false in
private theorem row_eval {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    (tails : Option (Fin n → Ty κ)) (r : Row (Φ := Φ) R L Γ) :
    ∃ f, RegionDenotes J M (row_typed ren tails r) f ∧
      f ≫ J.map (labelAppendSplit M (List.ofFn (family R tails)) L) =
        J.map p ≫ eval J M r ≫ J.map (coprod.map (𝟙 ExitObj) (labelChange M R tails)) := by
  induction r generalizing Δ ρ with
  | jump i a =>
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      cases tails with
      | none =>
          refine ⟨_, RegionDenotes.br (h := local_append R L i) da, ?_⟩
          simp only [eval, family, labelChange, coprod.map_id_id, J.map_id, Category.comp_id,
            Category.assoc, ← J.map_comp]
          erw [labelAppendSplit_local M R L i (local_append R L i) (local_label R i)]
      | some D =>
          refine ⟨_, RegionDenotes.br (h := local_append (family R (some D)) L i) (Denotes.inl (B := D i) da), ?_⟩
          simp only [eval, Category.assoc, ← J.map_comp, labelChange, coprod.inr_map]
          erw [labelAppendSplit_local M (family R (some D)) L i
            (local_append (family R (some D)) L i) (local_label (family R (some D)) i),
            label_embed_assoc M R D i]
          simp only [tag, Category.assoc]
  | exit i hit a =>
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      refine ⟨_, RegionDenotes.br (h := exit_append (family R tails) hit) da, ?_⟩
      simp only [eval, Category.assoc, ← J.map_comp, coprod.inl_map, Category.id_comp]
      erw [labelAppendSplit_exit M (family R tails) L hit (exit_append (family R tails) hit)]
  | @case Γ A B a l r ihl ihr =>
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      obtain ⟨fl, dl, left⟩ := ihl (ren.lift A) (p ▷ M.obj A) (lookup_liftRename M ren reads A)
      obtain ⟨fr, dr, right⟩ := ihr (ren.lift B) (p ▷ M.obj B) (lookup_liftRename M ren reads B)
      refine ⟨_, RegionDenotes.case da dl dr, ?_⟩
      simp only [eval, case_postcomp, left, right, Category.assoc]
      rw [case_pre_map]

private theorem cut_eq {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    (tails : Option (Fin n → Ty κ)) (r : Row (Φ := Φ) R L Γ)
    {f : J.obj (ctxObj M Δ) ⟶ J.obj (labelObj M (List.ofFn (family R tails) ++ L))}
    (w : RegionDenotes J M (row_typed ren tails r) f) :
    f ≫ J.map (labelAppendSplit M (List.ofFn (family R tails)) L) =
      J.map p ≫ eval J M r ≫ J.map (coprod.map (𝟙 ExitObj) (labelChange M R tails)) := by
  obtain ⟨_, d, computed⟩ := row_eval J M ren p reads tails r
  rw [(row_determined ren tails r).denotes_eq J M w d, computed]

theorem row_comparison {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    (D : Fin n → Ty κ) (r : Row (Φ := Φ) R L Γ)
    {ts : (r.region false id).HasType Γ (List.ofFn R ++ L)}
    {tl : (r.region true ρ).HasType Δ (List.ofFn (family R (some D)) ++ L)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    {g : J.obj (ctxObj M Δ) ⟶ J.obj (labelObj M (List.ofFn (family R (some D)) ++ L))}
    (small : RegionDenotes J M ts f) (wide : RegionDenotes J M tl g) :
    g ≫ J.map (labelAppendSplit M (List.ofFn (family R (some D))) L) =
      J.map p ≫ f ≫ J.map (labelAppendSplit M (List.ofFn R) L) ≫
        J.map (coprod.map (𝟙 ExitObj) (embedLabels M R D)) := by
  have before := cut_eq J M (Ren.id Γ) (𝟙 (ctxObj M Γ)) (fun _ _ _ => Category.id_comp _)
    none r small
  have after := cut_eq J M ren p reads (some D) r wide
  simp only [family, labelChange] at before
  erw [coprod.map_id_id, J.map_id, J.map_id, Category.id_comp, Category.comp_id] at before
  rw [← Category.assoc f, before]
  exact after

section Program

variable {k : Nat} {P : Fin (k + 1) → Ty κ} {K : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

local notation "Env" => ctxObj M Γ
local notation "Result" => labelObj M K
local notation "Local" => labelObj M (List.ofFn P)

private theorem dispatch_of_rows (roll : IterationRolling C)
    (p : Program (Φ := Φ) P K Γ) (tails : Option (Fin (k + 1) → Ty κ))
    (small : J.obj (Env ⊗ finiteLabelObj M P) ⟶ J.obj (Result ⨿ Local))
    (small_rows : ∀ i, J.map ((𝟙 Env) ⊗ₘ finiteLabelInject M P i) ≫ small =
      J.map (fst Env (M.obj (P i))) ≫ eval J M (p.blocks i))
    {e : J.obj Env ⟶ J.obj (labelObj M (List.ofFn (family P tails) ++ K))}
    {bs : ∀ i, J.obj (ctxObj M (family P tails i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn (family P tails) ++ K))}
    {large : J.obj (Env ⊗ finiteLabelObj M (family P tails)) ⟶
      J.obj (labelObj M (List.ofFn (family P tails) ++ K))}
    (entry : RegionDenotes J M (row_typed (Ren.id Γ) tails p.entry) e)
    (blocks : ∀ i, RegionDenotes J M
      (row_typed (Ren.wk Γ (family P tails i)) tails (p.blocks i)) (bs i))
    (rows : CollectiveDenotes J M Γ (family P tails) K bs large) :
    caseWithContext J
      (e ≫ J.map (labelAppendSplit M (List.ofFn (family P tails)) K)) (J.map (snd Env Result))
      (contextualLoop J
        (J.map ((𝟙 Env) ⊗ₘ labelObjToFinite M (family P tails)) ≫ large ≫
          J.map (labelAppendSplit M (List.ofFn (family P tails)) K))) =
    caseWithContext J (eval J M p.entry) (J.map (snd Env Result))
      (contextualLoop J (J.map (Env ◁ labelObjToFinite M P) ≫ small)) := by
  let S := family P tails
  let h := labelChange M P tails
  let hf := finiteChange M P tails
  let cut := labelAppendSplit M (List.ofFn S) K
  let inject (i : Fin (k + 1)) := payloadChange M P tails i
  obtain ⟨mid, mid_rows⟩ := collective_exists J M k Γ S (Result ⨿ Local)
    (fun i => J.map (fst Env (M.obj (S i))) ≫ eval J M (p.blocks i))
  have entry_eq : e ≫ J.map cut =
      eval J M p.entry ≫ J.map (coprod.map (𝟙 Result) h) := by
    have computed := cut_eq J M (Ren.id Γ) (𝟙 Env) (fun _ _ _ => Category.id_comp _)
      tails p.entry entry
    rw [J.map_id, Category.id_comp] at computed
    exact computed
  have before : J.map (Env ◁ hf) ≫ mid = small := by
    apply collective_ext J M k Γ P
    intro i
    rw [MonoidalCategory.id_tensorHom]
    have selected := small_rows i
    rw [MonoidalCategory.id_tensorHom] at selected
    rw [selected]
    have slide :
        J.map (Env ◁ finiteLabelInject M P i) ≫ J.map (Env ◁ hf) ≫ mid =
          J.map (Env ◁ inject i) ≫ J.map ((𝟙 Env) ⊗ₘ finiteLabelInject M S i) ≫ mid := by
      rw [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc, ← J.map_comp_assoc,
        ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
      exact congrArg (fun f => J.map (Env ◁ f) ≫ mid) (finite_change_inject M P tails i)
    erw [slide, mid_rows i, ← J.map_comp_assoc, CartesianMonoidalCategory.whiskerLeft_fst]
  have after : large ≫ J.map cut = mid ≫ J.map (coprod.map (𝟙 Result) h) := by
    apply collective_ext J M k Γ S
    intro i
    erw [← Category.assoc _ large, rows.restrict i, ← Category.assoc _ mid, mid_rows i, Category.assoc]
    exact cut_eq J M (Ren.wk Γ (S i)) (fst Env (M.obj (S i))) (fun _ _ _ => rfl) tails
      (p.blocks i) (blocks i)
  let middle := J.map (Env ◁ labelObjToFinite M S) ≫ mid
  have commute : J.map (Env ◁ h) ≫ middle = J.map (Env ◁ labelObjToFinite M P) ≫ small := by
    unfold middle
    rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp]
    erw [change_toFinite M P tails]
    rw [MonoidalCategory.whiskerLeft_comp, J.map_comp, Category.assoc, before]
  have computed := cfgDispatch_of_state_factorization J roll h (eval J M p.entry) middle
  rw [commute] at computed
  unfold middle at computed
  rw [Category.assoc] at computed
  rw [MonoidalCategory.id_tensorHom, entry_eq, ← Category.assoc _ large, Category.assoc, after]
  exact computed.symm

theorem program_agreement (roll : IterationRolling C) (p : Program (Φ := Φ) P K Γ) :
    ∃ f, ∀ (tails : Option (Fin (k + 1) → Ty κ)) (t : (p.region tails.isSome).HasType Γ K),
      RegionDenotes J M t f := by
  obtain ⟨small, small_rows⟩ := collective_exists J M k Γ P (Result ⨿ Local)
    (fun i => J.map (fst Env (M.obj (P i))) ≫ eval J M (p.blocks i))
  refine ⟨caseWithContext J (eval J M p.entry) (J.map (snd Env Result))
    (contextualLoop J (J.map (Env ◁ labelObjToFinite M P) ≫ small)), ?_⟩
  intro tails t
  let S := family P tails
  let e := row_typed (Ren.id Γ) tails p.entry
  let steps (i : Fin (k + 1)) := row_typed (Ren.wk Γ (S i)) tails (p.blocks i)
  obtain ⟨large, rows⟩ := collectiveDenotes_exists_succ J M k Γ S K (fun i => denoteRegion J M (steps i))
  have entry := denoteRegion_spec J M e
  have blocks (i : Fin (k + 1)) := denoteRegion_spec J M (steps i)
  have compared := dispatch_of_rows J M roll p tails small small_rows entry blocks rows
  exact compared ▸ RegionDenotes.cfg e steps entry blocks rows

end Program

end Graph

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof
