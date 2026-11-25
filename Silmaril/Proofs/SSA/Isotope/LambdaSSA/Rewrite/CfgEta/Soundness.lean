module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Closure
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies

/-! # Soundness of literal CFG η with shared tensor comparisons -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Region Region.CfgEta
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory.CartesianMonoidalCategory (snd)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
private theorem continuation_exists {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.HasType Γ L K σ) :
    ∃ k, ContinuationDenotes J M (Γ := Γ) (L := L) (K := K) σ k := by
  let E := ctxObj M Γ
  induction L generalizing σ with
  | nil =>
    refine ⟨J.map (snd E (labelObj M []) ≫
      Sigma.desc (fun i : Fin (([] : List τ).length) => i.elim0)), ?_⟩
    intro i A hi
    simp [At] at hi
  | cons A L ih =>
    let R : Fin 1 → τ := fun _ => A
    let split := labelAppendSplit M [A] L
    let hhead := hσ (show At (A :: L) 0 A from rfl)
    obtain ⟨tail, dtail⟩ := ih (σ := fun i => σ (i + 1)) (fun _ _ hi => hσ hi)
    let fromSingleton : labelObj M [A] ⟶ M.obj A :=
      Sigma.desc (fun i => eqToHom (congrArg M.obj (by
        obtain rfl := Fin.eq_zero i
        rfl)))
    have singleton : labelInject M 0 (show At [A] 0 A from rfl) ≫ fromSingleton = 𝟙 _ := by
      simp [fromSingleton, labelInject]
    let k := J.map (E ◁ split) ≫ distributeEnv J E (labelObj M L) (labelObj M [A]) ≫
      coprod.desc tail (J.map (E ◁ fromSingleton) ≫ denoteRegion J M hhead)
    refine ⟨k, ?_⟩
    intro i B hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      have route : labelInject M 0 hi ≫ split =
          labelInject M 0 (show At [A] 0 A from rfl) ≫ coprod.inr :=
        labelAppendSplit_local M R 0 L
      refine ⟨hhead, ?_⟩
      simp only [k, E, MonoidalCategory.id_tensorHom, ← J.map_comp_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp, route, MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc]
      simp only [distributeEnv, Category.assoc, distributeMap_inr_assoc, coprod.inr_desc]
      rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, singleton, MonoidalCategory.whiskerLeft_id]
      change RegionDenotes J M hhead (J.map (𝟙 (ctxObj M (A :: Γ))) ≫ denoteRegion J M hhead)
      rw [J.map_id, Category.id_comp]
      exact denoteRegion_spec J M hhead
    | succ i =>
      have htail : At L i B := hi
      have route : labelInject M (i + 1) hi ≫ split = labelInject M i htail ≫ coprod.inl := by
        have h := labelAppendSplit_exit M R htail
        change labelInject M (L := A :: L) (1 + i) (exitAt R htail) ≫ split =
          labelInject M i htail ≫ coprod.inl at h
        simpa only [Nat.add_comm 1 i] using h
      obtain ⟨h, d⟩ := dtail htail
      refine ⟨h, ?_⟩
      simp only [k, E, MonoidalCategory.id_tensorHom, ← J.map_comp_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp, route, MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc]
      simpa only [distributeEnv, Category.assoc, distributeMap_inl_assoc, coprod.inl_desc,
        MonoidalCategory.id_tensorHom] using d

variable [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
private theorem etaPost_sound
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {A : τ} {L K : LCtx τ} {entry block : Region Φ} {σ : Nat → Region Φ}
    (he : ValueBranches Γ entry (A :: L)) (hb : ValueBranches (A :: Γ) block (A :: L))
    (hσ : LSubst.HasType Γ L K σ)
    (h₁ : HasType Γ ((singleCfg entry block).lsubst σ) K)
    (h₂ : HasType Γ ((entry.lsubst (reentry block)).lsubst σ) K) :
    denoteRegion J M h₁ = denoteRegion J M h₂ := by
  let _ : FreydCategory.CentralUnit J := ⟨hu⟩
  let R : Fin 1 → τ := fun _ => A
  have vl : ValueBranches Γ (singleCfg entry block) L := .cfg R he (fun _ => hb)
  have vr := valueBranches_lsubst he (reentry_values hb)
  have hbase : denoteRegion J M vl.hasType = denoteRegion J M vr.hasType :=
    denoteRegion_cfgEta_sharedTensor J M shared R he.hasType (fun _ => hb.hasType)
      (PureBranches.of_valueBranches J M he) vr.hasType
  obtain ⟨k, dk⟩ := continuation_exists J M hσ
  rw [denoteRegion_lsubst_sharedTensor J M shared vl.hasType h₁ (PureBranches.of_valueBranches J M vl) dk,
    denoteRegion_lsubst_sharedTensor J M shared vr.hasType h₂ (PureBranches.of_valueBranches J M vr) dk, hbase]

theorem sound_sharedTensor
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  have common : ∃ (hr : HasType Γ r L) (hs : HasType Γ s L), ∃ f,
      RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
    clear hr hs
    induction h with
    | native h =>
      obtain ⟨hr, hs⟩ := h.typed
      exact ⟨hr, hs, _, denoteRegion_spec J M hr,
        (h.sound J M hu hr hs).symm ▸ denoteRegion_spec J M hs⟩
    | symm _ ih =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ih
      exact ⟨hs, hr, f, ds, dr⟩
    | trans _ _ ia ib =>
      obtain ⟨hr, hm, f, dr, dm⟩ := ia
      obtain ⟨_, hs, g, dm', ds⟩ := ib
      have eq : f = g := RegionTypingCoherent.denotes_eq (h := hm) dm dm'
      exact ⟨hr, hs, g, eq ▸ dr, ds⟩
    | let₁ ha _ ih =>
      obtain ⟨hr, hs, _, dr, ds⟩ := ih
      exact ⟨.let₁ ha hr, .let₁ ha hs, _, .let₁ (denote_spec J M ha) dr, .let₁ (denote_spec J M ha) ds⟩
    | let₂ ha _ ih =>
      obtain ⟨hr, hs, _, dr, ds⟩ := ih
      exact ⟨.let₂ ha hr, .let₂ ha hs, _, .let₂ (denote_spec J M ha) dr, .let₂ (denote_spec J M ha) ds⟩
    | case ha _ _ il ir =>
      obtain ⟨hl, hl', _, dl, dl'⟩ := il
      obtain ⟨hr, hr', _, dr, dr'⟩ := ir
      exact ⟨.case ha hl hr, .case ha hl' hr', _, .case (denote_spec J M ha) dl dr,
        .case (denote_spec J M ha) dl' dr'⟩
    | @cfg n _ _ _ _ _ _ R _ _ ie ib =>
      obtain ⟨he, he', f, de, de'⟩ := ie
      choose hb hb' fb db using ib
      cases n with
      | zero =>
        exact ⟨.cfg R he hb, .cfg R he' hb', f, .cfgZero he hb de, .cfgZero he' hb' de'⟩
      | succ n =>
        obtain ⟨_, dc⟩ := collectiveDenotes_exists_succ J M n _ R _ fb
        exact ⟨.cfg R he hb, .cfg R he' hb', _,
          .cfg he hb de (fun i => (db i).1) dc, .cfg he' hb' de' (fun i => (db i).2) dc⟩
    | etaPost he hb hσ =>
      obtain ⟨ht, hs⟩ := (Eqv.etaPost he hb hσ).typed
      exact ⟨ht, hs, _, denoteRegion_spec J M ht,
        (etaPost_sound J M hu shared he hb hσ ht hs).symm ▸ denoteRegion_spec J M hs⟩
  obtain ⟨_, _, _, dr, ds⟩ := common
  exact (RegionDenotes.eq_denote (h := hr) J M dr).symm.trans
    (RegionDenotes.eq_denote (h := hs) J M ds)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
