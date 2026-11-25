module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Soundness

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Agreement

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ bind_of)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local notation "catBind" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

private theorem envFrom_envTo {Γ : VCtx τ} (ρ : Monadic.Env Γ) :
    envFromCategorical (envToCategorical ρ) = ρ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

private theorem envTo_surjective (Γ : VCtx τ) :
    Function.Surjective (envToCategorical (Γ := Γ)) := by
  intro ρ
  refine ⟨envFromCategorical ρ, ?_⟩
  induction Γ with
  | nil => rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

theorem categoricalRegion_bound_lsubst_graph_proof
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    {hr : Region.HasType Γ r L} {f : Monadic.Env Γ → m (Monadic.LabelDen L)}
    (df : Monadic.RegionDenotes ε hr f)
    (k : Monadic.Continuation (m := m) Γ L K) (d : k.Denotes (ε := ε) σ) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    let J := typeJ (m := m)
    let T := Categorical.ofMonadicTypeModel (τ := τ)
    ∃ F, Categorical.RegionDenotes J T hr F ∧
      ∃ hs : Region.HasType Γ (r.bindBranchArguments.lsubst σ) K,
        Categorical.RegionDenotes J T hs (catBind J F (continuationArrow k)) := by
  dsimp only
  let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  obtain ⟨hs, ds⟩ := df.bound_lsubst_proof d
  obtain ⟨F, dF, hF⟩ := regionDenotes_toCategorical df
  obtain ⟨G, dG, hG⟩ := regionDenotes_toCategorical ds
  have eq : G = catBind (typeJ (m := m)) F (continuationArrow k) := by
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext γ
    obtain ⟨ρ, rfl⟩ := envTo_surjective Γ γ
    have hFR := congrFun hF ρ
    have hGR := congrFun hG ρ
    rw [bind_of]
    let c : Monadic.CategoricalLabelDen L → m (Monadic.CategoricalLabelDen K) :=
      fun z => (continuationArrow k).of (envToCategorical ρ, z)
    change G.of (envToCategorical ρ) =
      (show m (Monadic.CategoricalLabelDen L) from F.of (envToCategorical ρ)) >>= c
    refine hGR.trans (Eq.trans ?_ (congrArg (fun x : m (Monadic.CategoricalLabelDen L) => x >>= c) hFR).symm)
    change ((f ρ >>= k ρ) >>= fun x => pure (Monadic.LabelValue.categoricalEquiv K x)) =
      ((f ρ >>= fun x => pure (Monadic.LabelValue.categoricalEquiv L x)) >>= fun z =>
        k (envFromCategorical (envToCategorical ρ)) ((Monadic.LabelValue.categoricalEquiv L).symm z) >>=
          fun y => pure (Monadic.LabelValue.categoricalEquiv K y))
    simp only [envFrom_envTo, bind_assoc, pure_bind, Equiv.symm_apply_apply]
  exact ⟨F, dF, hs, eq ▸ dG⟩

theorem categoricalRegion_bound_lsubst_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L)
    (hs : Region.HasType Γ (r.bindBranchArguments.lsubst σ) K)
    (k : Monadic.Continuation (m := m) Γ L K) (d : k.Denotes (ε := ε) σ) :
    categoricalRegionDenote (ε := ε) (m := m) hs =
      catBind (typeJ (m := m)) (categoricalRegionDenote (ε := ε) (m := m) hr) (continuationArrow k) := by
  let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  let _ : Categorical.RegionTypingCoherent (Φ := Φ)
      (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) := coherent
  obtain ⟨F, dF, _, dG⟩ := categoricalRegion_bound_lsubst_graph_proof
    (Monadic.Region.denote_spec (ε := ε) (m := m) hr) k d
  have eq := Categorical.RegionDenotes.eq_denote _ _ dF
  have result := Categorical.RegionDenotes.eq_denote _ _ (h := hs) dG
  simp only [categoricalRegionDenote, ← eq]
  exact result.symm

omit [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m] in
theorem continuationArrow_comp_proof {Γ : VCtx τ} {L K H : LCtx τ}
    (first : Monadic.Continuation (m := m) Γ L K)
    (after : Monadic.Continuation (m := m) Γ K H) :
    let E := Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ
    let J := typeJ (m := m)
    let forget : (E × Monadic.CategoricalLabelDen L) × Monadic.CategoricalLabelDen K →
        E × Monadic.CategoricalLabelDen K := fun p => (p.1.1, p.2)
    continuationArrow (first.comp after) =
      catBind J (continuationArrow first) (J.map (↾forget) ≫ continuationArrow after) := by
  let E := Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ
  let J := typeJ (m := m)
  let forget : (E × Monadic.CategoricalLabelDen L) × Monadic.CategoricalLabelDen K →
      E × Monadic.CategoricalLabelDen K := fun p => (p.1.1, p.2)
  let rest := J.map (↾forget) ≫ continuationArrow after
  have hrest (p : (E × Monadic.CategoricalLabelDen L) × Monadic.CategoricalLabelDen K) :
      rest.of p = (continuationArrow after).of (forget p) := by
    dsimp only [rest]
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    change ((pure (forget p) : m (E × Monadic.CategoricalLabelDen K)) >>= fun q =>
        (show m (Monadic.CategoricalLabelDen H) from (continuationArrow after).of q)) =
      (show m (Monadic.CategoricalLabelDen H) from (continuationArrow after).of (forget p))
    rw [pure_bind]
  dsimp only
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  funext p
  rw [bind_of]
  let γ : Monadic.Env Γ := envFromCategorical p.1
  let x : Monadic.LabelDen L := (Monadic.LabelValue.categoricalEquiv L).symm p.2
  change ((first γ x >>= after γ) >>= fun y => pure (Monadic.LabelValue.categoricalEquiv H y)) =
    ((first γ x >>= fun y => pure (Monadic.LabelValue.categoricalEquiv K y)) >>= fun q =>
      (show m (Monadic.CategoricalLabelDen H) from rest.of (p, q)))
  rw [bind_assoc, bind_assoc]
  apply bind_congr
  intro y
  rw [pure_bind, hrest]
  change (after γ y >>= fun z => pure (Monadic.LabelValue.categoricalEquiv H z)) =
    after γ ((Monadic.LabelValue.categoricalEquiv K).symm
      (Monadic.LabelValue.categoricalEquiv K y)) >>= fun z => pure (Monadic.LabelValue.categoricalEquiv H z)
  rw [Equiv.symm_apply_apply]

end Silmaril.Isotope.LambdaSSA.Semantics.Agreement
