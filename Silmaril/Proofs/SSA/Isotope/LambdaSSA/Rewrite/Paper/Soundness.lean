module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Soundness.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Codiagonal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Soundness.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Step.Soundness.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Assembly.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms

/-! # Denotational soundness of the opt-in λSSA closure -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

omit [RegionTypingCoherent (Φ := Φ) J M] [FreydCategory.CentralUnit J] in
private theorem common_of_eq {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    {hr : HasType Γ r L} {hs : HasType Γ s L}
    (h : denoteRegion J M hr = denoteRegion J M hs) :
    ∃ (hr : HasType Γ r L) (hs : HasType Γ s L), ∃ f,
      RegionDenotes J M hr f ∧ RegionDenotes J M hs f :=
  ⟨hr, hs, _, denoteRegion_spec J M hr, h.symm ▸ denoteRegion_spec J M hs⟩

omit [FreydCategory.CentralUnit J] in
private theorem common_eq {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    {hr : HasType Γ r L} {hs : HasType Γ s L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (dr : RegionDenotes J M hr f) (ds : RegionDenotes J M hs f) :
    denoteRegion J M hr = denoteRegion J M hs :=
  (dr.eq_denote J M).symm.trans (ds.eq_denote J M)

theorem sound
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  have common : ∃ (hr : HasType Γ r L) (hs : HasType Γ s L), ∃ f,
      RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
    clear hr hs
    induction h with
    | cfgEta h =>
      exact common_of_eq J M (h.sound_sharedTensor J M
        (FreydCategory.CentralUnit.unit_central (J := J)) shared h.typed.1 h.typed.2)
    | productBeta h =>
      obtain ⟨_, dr, ds⟩ := h.denotes J M
      exact ⟨_, _, _, dr, ds⟩
    | productEta h =>
      obtain ⟨_, dr, ds⟩ := h.denotes J M
      exact ⟨_, _, _, dr, ds⟩
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
    | @lsubstCongr Γ p L σ υ K hp h ih =>
      have hσ : LSubst.HasType Γ L K σ := fun _ _ hi => (h hi).typed.1
      obtain ⟨k, dk⟩ := ContinuationDenotes.exists_of_typed M J hσ
      have dk' : ContinuationDenotes J M υ k := by
        intro i A hi
        obtain ⟨_, ds⟩ := dk hi
        obtain ⟨_, ht, _, ds', dt⟩ := ih hi
        exact ⟨ht, RegionTypingCoherent.denotes_eq ds' ds ▸ dt⟩
      apply common_of_eq J M
      exact (denoteRegion_lsubst_sharedTensor J M shared hp.hasType
        (hp.hasType.lsubst hσ) (PureBranches.of_valueBranches J M hp) dk).trans
        (denoteRegion_lsubst_sharedTensor J M shared hp.hasType
          (hp.hasType.lsubst (fun _ _ hi => (h hi).typed.2))
          (PureBranches.of_valueBranches J M hp) dk').symm
    | lsubstPost _ hr hs hσ ih =>
      obtain ⟨_, _, _, dr, ds⟩ := ih
      obtain ⟨_, dk⟩ := ContinuationDenotes.exists_of_typed M J hσ
      apply common_of_eq J M (hr := hr.hasType.lsubst hσ) (hs := hs.hasType.lsubst hσ)
      rw [denoteRegion_lsubst_sharedTensor J M shared hr.hasType _ (PureBranches.of_valueBranches J M hr) dk,
        denoteRegion_lsubst_sharedTensor J M shared hs.hasType _ (PureBranches.of_valueBranches J M hs) dk,
        common_eq J M dr ds]
    | substVars _ hθ ih =>
      obtain ⟨_, _, f, dr, ds⟩ := ih
      obtain ⟨k, transport⟩ := RegionDenotes.substBranchValues J M hθ
      obtain ⟨hr, dr'⟩ := transport dr
      obtain ⟨hs, ds'⟩ := transport ds
      exact ⟨hr, hs, J.map k ≫ f, dr', ds'⟩
    | renameLabels _ hρ ih =>
      obtain ⟨_, _, _, dr, ds⟩ := ih
      exact ⟨_, _, _, dr.renameLabels J M hρ, ds.renameLabels J M hρ⟩
    | collapsePost he hp hσ =>
      exact common_of_eq J M (CfgEta.Codiagonal.collapsePost M J shared he hp hσ)
    | uniform he hp hq ha _ ih =>
      obtain ⟨_, da⟩ := ha.denotes_map J M
      obtain ⟨hl, hr, _, dl, dr⟩ := ih
      exact common_of_eq J M (CfgEta.Uniformity.sound_entry_of_denotations M J shared he hp hq da
        hl hr (common_eq J M dl dr))
  obtain ⟨_, _, _, dr, ds⟩ := common
  exact common_eq J M dr ds

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
