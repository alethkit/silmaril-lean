module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Pure.Thms

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Agreement

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

local notation "J" => typeJ (m := m)
local notation "T" => Categorical.ofMonadicTypeModel (τ := τ)
local notation "catBind" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

private theorem envTo_envFrom {Γ : VCtx τ} (ρ : Categorical.ctxObj T Γ) :
    envToCategorical (envFromCategorical ρ) = ρ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

omit [Iterate m] [LawfulElgotMonad m] in
private theorem restrict_apply {Γ : VCtx τ} {L K : LCtx τ}
    (k : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K)) {i : Nat} {A : τ} (h : At L i A)
    (ρ : Categorical.ctxObj T Γ) (a : TyDen A) :
    ((J).map ((𝟙 (Categorical.ctxObj T Γ)) ⊗ₘ Categorical.labelInject T i h) ≫ k).of (ρ, a) =
      k.of (ρ, Categorical.labelInject T i h a) := by
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  change ((pure (ρ, Categorical.labelInject T i h a) :
    m (Categorical.ctxObj T Γ × Monadic.CategoricalLabelDen L)) >>= fun p =>
      (show m (Monadic.CategoricalLabelDen K) from k.of p)) = k.of _
  rw [pure_bind]

theorem continuationArrow_denotes_proof {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {k : Monadic.Continuation (m := m) Γ L K} (d : k.Denotes (ε := ε) σ) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ (continuationArrow k) := by
  dsimp only
  let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  intro i A h
  obtain ⟨hr, dr⟩ := d h
  obtain ⟨F, dF, hF⟩ := regionDenotes_toCategorical dr
  refine ⟨hr, ?_⟩
  have eq : (J).map ((𝟙 (Categorical.ctxObj T Γ)) ⊗ₘ Categorical.labelInject T i h) ≫
      continuationArrow k = F := by
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext p
    obtain ⟨ρ, a⟩ := p
    rw [restrict_apply]
    have hf := congrFun hF (envFromCategorical ρ, a)
    rw [show envToCategorical (Γ := A :: Γ) (envFromCategorical ρ, a) = (ρ, a) from
      Prod.ext (envTo_envFrom ρ) rfl] at hf
    refine Eq.trans ?_ hf.symm
    change (k (envFromCategorical ρ) ((Monadic.LabelValue.categoricalEquiv L).symm
      (Categorical.labelInject T i h a)) >>= _) =
        k (envFromCategorical ρ) (Monadic.LabelValue.inject i h a) >>= _
    rw [← Monadic.LabelValue.categoricalEquiv_inject, Equiv.symm_apply_apply]
  exact eq.symm ▸ dF

omit [Iterate m] [LawfulElgotMonad m] in
private theorem continuation_ext {Γ : VCtx τ} {L K : LCtx τ}
    {k₁ k₂ : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K)}
    (h : ∀ ⦃i A⦄ (hl : At L i A),
      (J).map ((𝟙 (Categorical.ctxObj T Γ)) ⊗ₘ Categorical.labelInject T i hl) ≫ k₁ =
      (J).map ((𝟙 (Categorical.ctxObj T Γ)) ⊗ₘ Categorical.labelInject T i hl) ≫ k₂) :
    k₁ = k₂ := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  funext p
  obtain ⟨ρ, z⟩ := p
  obtain ⟨⟨i, a⟩, rfl⟩ := (Monadic.categoricalSigmaEquiv L).surjective z
  have hl : At L i (L.get i) := List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩
  have injection : Categorical.labelInject T i hl a = Monadic.categoricalSigmaEquiv L ⟨i, a⟩ := by
    rw [Monadic.categoricalSigmaEquiv_apply, Categorical.labelInject_eq_sigma]
    simp
    rfl
  have eq := congrArg (fun k => k.of (ρ, a)) (h hl)
  simpa only [restrict_apply, injection] using eq

theorem continuationArrow_exists_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (k : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K)) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ k →
      ∃ c : Monadic.Continuation (m := m) Γ L K, c.Denotes (ε := ε) σ ∧ continuationArrow c = k := by
  dsimp only
  let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  let _ : Categorical.RegionTypingCoherent (Φ := Φ) J T := coherent
  intro dk
  obtain ⟨c, dc⟩ := Monadic.continuation_exists (ε := ε) (m := m) (fun _ _ h => (dk h).choose)
  refine ⟨c, dc, continuation_ext ?_⟩
  intro i A h
  obtain ⟨_, dC⟩ := continuationArrow_denotes_proof dc h
  obtain ⟨_, dK⟩ := dk h
  exact Categorical.RegionTypingCoherent.denotes_eq dC dK

theorem categoricalRegion_lsubst_of_continuationDenotes_graph_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.lsubst σ) K)
    (pureBranches : Monadic.PureBranches (m := m) ε Γ r L)
    (k : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K)) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ k →
      ∃ F, Categorical.RegionDenotes J T hr F ∧ Categorical.RegionDenotes J T hs (catBind J F k) := by
  dsimp only
  intro dk
  obtain ⟨c, dc, rfl⟩ := continuationArrow_exists_proof coherent k dk
  exact categoricalRegion_lsubst_graph hr hs pureBranches c dc

theorem categoricalRegion_lsubst_of_continuationDenotes_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.lsubst σ) K)
    (pureBranches : Monadic.PureBranches (m := m) ε Γ r L)
    (k : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K)) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ k →
      categoricalRegionDenote (ε := ε) (m := m) hs =
        catBind J (categoricalRegionDenote (ε := ε) (m := m) hr) k := by
  dsimp only
  intro dk
  obtain ⟨c, dc, rfl⟩ := continuationArrow_exists_proof coherent k dk
  exact categoricalRegion_lsubst coherent hr hs pureBranches c dc

theorem continuationDenotes_compose_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K H : LCtx τ} {σ υ : Nat → Region Φ}
    (first : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K))
    (after : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen K) ⟶
      (J).obj (Monadic.CategoricalLabelDen H))
    (pureBranches : ∀ ⦃i A⦄, At L i A → Monadic.PureBranches (m := m) ε (A :: Γ) (σ i) K) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ first → Categorical.ContinuationDenotes J T υ after →
      Categorical.ContinuationDenotes J T (Region.compLSubst σ υ)
        (Categorical.composeContinuations J T (Γ := Γ) (L := L) (K := K) (H := H) first after) := by
  dsimp only
  intro dFirst dAfter
  obtain ⟨c, dc, rfl⟩ := continuationArrow_exists_proof coherent first dFirst
  obtain ⟨k, dk, rfl⟩ := continuationArrow_exists_proof coherent after dAfter
  have den := continuationArrow_denotes_proof (continuationDenotes_compLSubst coherent dc dk pureBranches)
  rw [continuationArrow_comp] at den
  exact den

end Silmaril.Isotope.LambdaSSA.Semantics.Agreement
