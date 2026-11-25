module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Denotational soundness of the opt-in constructor-pair equation -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.ProductBeta
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false

/-- The alternate decoder's constructor-pair β is semantically valid for
any fixed exactly typed body, with simultaneous substitution for both slots. -/
private theorem let₂_constructor_beta_common {Γ : VCtx τ} {A B : τ} {L : LCtx τ}
    {a b : Tm Φ} {r : Region Φ}
    (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B)
    (hr : Region.HasType (B :: A :: Γ) r L) :
    ∃ (ht : Region.HasType Γ (r.substVars (Tm.consSubst b (Tm.singleSubst a))) L)
      (f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)),
      RegionDenotes J M (.let₂ (.pair ha.hasType hb.hasType) hr) f ∧
        RegionDenotes J M ht f := by
  obtain ⟨p, da⟩ := ha.denotes_map J M
  obtain ⟨q, db⟩ := hb.denotes_map J M
  obtain ⟨f, dr⟩ := regionDenotes_exists J M hr
  let k : ctxObj M Γ ⟶ ctxObj M (B :: A :: Γ) := lift (lift (𝟙 (ctxObj M Γ)) p) q
  have hs : SubstDenotes J M
      (Γ := B :: A :: Γ) (Δ := Γ) (Tm.consSubst b (Tm.singleSubst a)) k := by
    intro i T hi
    cases i with
    | zero =>
      have e : B = T := Option.some.inj hi
      subst T
      refine ⟨hb.hasType, ?_⟩
      simpa only [lookup, k, lift_snd] using db
    | succ i =>
      cases i with
      | zero =>
        have e : A = T := Option.some.inj hi
        subst T
        refine ⟨ha.hasType, ?_⟩
        simpa only [lookup, k, lift_fst_assoc, lift_snd] using da
      | succ i =>
        refine ⟨.var (i := i) hi, ?_⟩
        simpa only [lookup, k, lift_fst_assoc, Category.id_comp] using
          (Denotes.var (J := J) (M := M) (Φ := Φ) (i := i) (show At Γ i T from hi))
  obtain ⟨ht, dt⟩ := regionDenotes_subst J M dr hs
  have dPair := Denotes.pair da db
  rw [pair_map, ← J.map_comp] at dPair
  have d := RegionDenotes.let₂ dPair dr
  refine ⟨ht, _, ?_, dt⟩
  simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_map, ctxPairIso, Iso.symm_hom,
    MonoidalCategory.id_tensorHom, Category.assoc, ← J.map_comp_assoc, lift_whiskerLeft_assoc,
    Iso.inv_hom_id, Category.comp_id, lift_lift_associator_inv, k] using d

theorem step_denotes
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Step Γ r s L) :
    ∃ f, RegionDenotes J M h.typed.1 f ∧ RegionDenotes J M h.typed.2 f := by
  cases h with
  | let₂Beta ha hb hr =>
    obtain ⟨_, f, ds, dt⟩ := let₂_constructor_beta_common J M ha hb hr
    exact ⟨f, ds, dt⟩

private theorem link_sound [RegionTypingCoherent (Φ := Φ) J M]
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Relation.SymmGen (fun r s => CfgEta.Eqv Γ r s L ∨ Step Γ r s L) r s)
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  rcases h with (h | h) | (h | h)
  · exact h.sound_sharedTensor J M hu shared hr hs
  · obtain ⟨_, dr, ds⟩ := step_denotes J M h
    exact (dr.eq_denote J M).symm.trans (ds.eq_denote J M)
  · exact (h.sound_sharedTensor J M hu shared hs hr).symm
  · obtain ⟨_, ds, dr⟩ := step_denotes J M h
    exact (dr.eq_denote J M).symm.trans (ds.eq_denote J M)

theorem eqv_sound_sharedTensor
    [RegionTypingCoherent (Φ := Φ) J M]
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L)
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  induction h with
  | single h => exact link_sound J M hu shared h hr hs
  | tail _ h ih =>
    have step : Eqv Γ _ _ L := .single h
    exact (ih step.typed.1).trans (link_sound J M hu shared h step.typed.1 hs)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta
