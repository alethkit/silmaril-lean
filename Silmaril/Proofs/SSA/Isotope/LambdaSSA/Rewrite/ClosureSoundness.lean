module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

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
  [RegionTypingCoherent (Φ := Φ) J M]

theorem substitutionEquiv_common
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Region.SubstitutionEquiv Γ r s L) :
    ∃ (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L), ∃ f,
      RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  induction h with
  | base h =>
    obtain ⟨hr, hs⟩ := h.typed
    exact ⟨hr, hs, _, denoteRegion_spec J M hr,
      (h.sound J M hr hs).symm ▸ denoteRegion_spec J M hs⟩
  | symm _ ih =>
    obtain ⟨hr, hs, f, dr, ds⟩ := ih
    exact ⟨hs, hr, f, ds, dr⟩
  | trans _ _ ihr ihs =>
    obtain ⟨hr, hs, f, dr, ds⟩ := ihr
    obtain ⟨_, ht, g, ds', dt⟩ := ihs
    have hfg : f = g := RegionTypingCoherent.denotes_eq (h := hs) ds ds'
    exact ⟨hr, ht, g, hfg ▸ dr, dt⟩
  | let₁ ha _ ih =>
    obtain ⟨hr, hs, _, dr, ds⟩ := ih
    have da := denote_spec J M ha
    exact ⟨.let₁ ha hr, .let₁ ha hs, _, .let₁ da dr, .let₁ da ds⟩
  | let₂ ha _ ih =>
    obtain ⟨hr, hs, _, dr, ds⟩ := ih
    have da := denote_spec J M ha
    exact ⟨.let₂ ha hr, .let₂ ha hs, _, .let₂ da dr, .let₂ da ds⟩
  | case ha _ _ ihl ihr =>
    obtain ⟨hl, hl', _, dl, dl'⟩ := ihl
    obtain ⟨hr, hr', _, dr, dr'⟩ := ihr
    have da := denote_spec J M ha
    exact ⟨.case ha hl hr, .case ha hl' hr', _, .case da dl dr, .case da dl' dr'⟩
  | @cfg n _ _ _ _ _ _ R _ _ ihe ihb =>
    obtain ⟨he, he', fe, de, de'⟩ := ihe
    choose hb hb' fb db using ihb
    cases n with
    | zero =>
      exact ⟨.cfg R he hb, .cfg R he' hb', fe, .cfgZero he hb de, .cfgZero he' hb' de'⟩
    | succ n =>
      obtain ⟨_, dc⟩ := collectiveDenotes_exists_succ J M n _ R _ fb
      exact ⟨.cfg R he hb, .cfg R he' hb', _,
        .cfg he hb de (fun i => (db i).1) dc, .cfg he' hb' de' (fun i => (db i).2) dc⟩
  | letValue ha hr =>
    obtain ⟨ht, f, ds, dt⟩ := letValue_common J M ha hr
    exact ⟨_, ht, f, ds, dt⟩
  | cfgOutward R hr hb =>
    have hs := (Region.SubstitutionEquiv.cfgOutward R hr hb).typed.1
    exact ⟨hs, hr, _, denoteRegion_cfgOutward J M hu R hr hb hs ▸ denoteRegion_spec J M hs,
      denoteRegion_spec J M hr⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
