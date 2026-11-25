module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgLinkedEta
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect

/-! # Sequencing a payload router with a linked CFG -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)
open CategoryTheory.CartesianMonoidalCategory (fst snd)
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.SSA (Ren)


private theorem weakenReentry {Φ : Type u₄} {n : Nat} (blocks : Fin n → Region Φ) :
    Region.liftLSubstVars (Region.cfgEntryContinuations blocks) =
      Region.cfgEntryContinuations (fun i => (blocks i).renameVars (lift Nat.succ)) := by
  funext i
  simp only [Region.liftLSubstVars, Region.cfgEntryContinuations, Region.renameVars, Tm.rename]
  congr 1
  funext j
  rw [Region.renameVars_comp, Region.renameVars_comp]
  congr 1
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
private theorem cfgContinuations_denotes {n : Nat} {Γ : VCtx τ} {P L : LCtx τ}
    (R : Fin n → τ) {next : Nat → Region Φ} {blocks : Fin n → Region Φ}
    (hb : ∀ j, Region.HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L))
    (q : labelObj M P ⟶ labelObj M (List.ofFn R ++ L))
    (dn : ContinuationDenotes J M next (J.map (snd (ctxObj M Γ) (labelObj M P) ≫ q)))
    {k : J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R ++ L)) ⟶ J.obj (labelObj M L)}
    (dk : ContinuationDenotes J M (Region.cfgEntryContinuations blocks) k) :
    ContinuationDenotes J M (Region.cfgContinuations blocks next)
      (J.map (ctxObj M Γ ◁ q) ≫ k) := by
  intro i A hi
  let E := ctxObj M Γ
  let D := ctxObj M (A :: Γ)
  let S := labelObj M (List.ofFn R ++ L)
  let j := labelInject M i hi
  let π : D ⟶ E := fst E (M.obj A)
  let payload : D ⟶ S := snd E (M.obj A) ≫ j ≫ q
  obtain ⟨he, de⟩ := dn hi
  let hw (i : Fin n) := (hb i).renameVars ((Ren.wk Γ A).lift (R i))
  let hcfg := Region.HasType.cfg R he hw
  have ht := he.linkExits (Region.cfgEntryContinuations_hasType R hw)
  have hdk := dk.weakenCapture J M A
  rw [weakenReentry] at hdk
  have hpayload : denoteRegion J M he = J.map payload := by
    rw [← de.eq_denote J M, ← J.map_comp]
    simp only [payload, j, MonoidalCategory.id_tensorHom, ← Category.assoc]
    rw [CartesianMonoidalCategory.whiskerLeft_snd]
  have hproj : CartesianMonoidalCategory.lift (𝟙 D) payload ≫ (π ▷ S) =
      E ◁ (j ≫ q) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        CartesianMonoidalCategory.whiskerLeft_fst]
      simp [π]
    · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        CartesianMonoidalCategory.whiskerLeft_snd]
      simp [payload]
  have hden : denoteRegion J M hcfg = J.map (E ◁ (j ≫ q)) ≫ k := by
    rw [denoteRegion_cfgLinkedEta J M R he hw ht, denoteRegion_linkExits J M he ht hdk,
      hpayload]
    simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map, ← J.map_comp_assoc]
    change J.map (CartesianMonoidalCategory.lift (𝟙 D) payload ≫ (π ▷ S)) ≫ k = _
    rw [hproj]
  refine ⟨hcfg, ?_⟩
  have d := denoteRegion_spec J M hcfg
  rw [hden] at d
  simpa only [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp] using d

set_option backward.isDefEq.respectTransparency false in
theorem linked_cfg_sequencing {n : Nat} {Γ : VCtx τ} {P L : LCtx τ}
    {p : Region Φ} (R : Fin n → τ) {next : Nat → Region Φ} {blocks : Fin n → Region Φ}
    (hp : Region.HasType Γ p P)
    (hl : Region.HasType Γ (p.linkExits P next) (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (q : labelObj M P ⟶ labelObj M (List.ofFn R ++ L))
    (dn : ContinuationDenotes J M next (J.map (snd (ctxObj M Γ) (labelObj M P) ≫ q)))
    (hr : Region.HasType Γ (p.linkExits P (Region.cfgContinuations blocks next)) L) :
    denoteRegion J M (.cfg R hl hb) = denoteRegion J M hr := by
  obtain ⟨ht, _, k, dl, dt, dk⟩ := cfg_linked_eta_common J M R hl hb
  have hu := FreydCategory.CentralUnit.unit_central (J := J)
  have hleft : denoteRegion J M hl = denoteRegion J M hp ≫ J.map q := by
    rw [denoteRegion_linkExits J M hp hl dn]
    simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, J.map_comp, ← Category.assoc, extend_snd J hu]
  rw [← dl.eq_denote J M, dt.eq_denote J M, denoteRegion_linkExits J M hl ht dk,
    denoteRegion_linkExits J M hp hr (cfgContinuations_denotes J M R hb q dn dk), hleft]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_post_map, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
