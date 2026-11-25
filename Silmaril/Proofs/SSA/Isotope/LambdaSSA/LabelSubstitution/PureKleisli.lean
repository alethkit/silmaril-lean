module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Pure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Pure
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Kleisli
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Soundness

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Agreement

open CategoryTheory Silmaril.Elgot Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

local notation "catBind" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

theorem categoricalRegion_lsubst_graph_proof
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.lsubst σ) K)
    (pureBranches : Monadic.PureBranches (m := m) ε Γ r L)
    (k : Monadic.Continuation (m := m) Γ L K) (d : k.Denotes (ε := ε) σ) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    let J := typeJ (m := m)
    let T := Categorical.ofMonadicTypeModel (τ := τ)
    ∃ F, Categorical.RegionDenotes J T hr F ∧
      Categorical.RegionDenotes J T hs (catBind J F (continuationArrow k)) := by
  obtain ⟨_, _, _, df, ds⟩ := Monadic.pure_lsubst_proof pureBranches d
  exact categoricalRegion_bind_graph_proof df ds

theorem categoricalRegion_lsubst_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.lsubst σ) K)
    (pureBranches : Monadic.PureBranches (m := m) ε Γ r L)
    (k : Monadic.Continuation (m := m) Γ L K) (d : k.Denotes (ε := ε) σ) :
    categoricalRegionDenote (ε := ε) (m := m) hs =
      catBind (typeJ (m := m)) (categoricalRegionDenote (ε := ε) (m := m) hr) (continuationArrow k) := by
  let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  let _ : Categorical.RegionTypingCoherent (Φ := Φ)
      (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) := coherent
  obtain ⟨F, dF, dG⟩ := categoricalRegion_lsubst_graph_proof hr hs pureBranches k d
  have eq := Categorical.RegionDenotes.eq_denote _ _ dF
  have result := Categorical.RegionDenotes.eq_denote _ _ dG
  simp only [categoricalRegionDenote, ← eq]
  exact result.symm

private theorem regionDenotes_eq
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {hr : Region.HasType Γ r L}
    {f g : Monadic.Env Γ → m (Monadic.LabelDen L)}
    (df : Monadic.RegionDenotes ε hr f) (dg : Monadic.RegionDenotes ε hr g) : f = g := by
  let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  let J := typeJ (m := m)
  let T := Categorical.ofMonadicTypeModel (τ := τ)
  let _ : Categorical.RegionTypingCoherent (Φ := Φ) J T := coherent
  obtain ⟨F, dF, hF⟩ := regionDenotes_toCategorical df
  obtain ⟨G, dG, hG⟩ := regionDenotes_toCategorical dg
  have eq := Categorical.RegionTypingCoherent.denotes_eq (J := J) (M := T) dF dG
  funext ρ
  have encoded := (congrFun hF ρ).symm.trans
    ((congrArg (fun F => F.of (envToCategorical ρ)) eq).trans (congrFun hG ρ))
  let decode := fun x => (pure ((Monadic.LabelValue.categoricalEquiv L).symm x) :
    m (Monadic.LabelDen L))
  simpa only [decode, bind_assoc, pure_bind, Equiv.symm_apply_apply, bind_pure] using
    congrArg (fun x => x >>= decode) encoded

theorem continuationDenotes_compLSubst_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K H : LCtx τ} {σ υ : Nat → Region Φ}
    {first : Monadic.Continuation (m := m) Γ L K}
    {after : Monadic.Continuation (m := m) Γ K H}
    (dFirst : first.Denotes (ε := ε) σ) (dAfter : after.Denotes (ε := ε) υ)
    (pureBranches : ∀ ⦃i A⦄, At L i A → Monadic.PureBranches (m := m) ε (A :: Γ) (σ i) K) :
    (first.comp after).Denotes (ε := ε) (Region.compLSubst σ υ) := by
  intro i A h
  obtain ⟨_, df⟩ := dFirst h
  obtain ⟨_, hs, _, dg, ds⟩ :=
    Monadic.pure_lsubst_proof (pureBranches h) (Monadic.Continuation.Denotes.liftVars_proof dAfter A)
  rw [regionDenotes_eq coherent dg df] at ds
  exact ⟨hs, ds⟩

end Silmaril.Isotope.LambdaSSA.Semantics.Agreement
