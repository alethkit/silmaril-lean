module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Dispatcher
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.LabelRenaming

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Elgot Silmaril.DeBruijn
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]

private theorem env_ext {Γ : VCtx τ} (γ δ : Env Γ)
    (eq : ∀ i A (h : At Γ i A), Env.get γ i h = Env.get δ i h) : γ = δ := by
  induction Γ with
  | nil => cases γ; cases δ; rfl
  | cons B Γ ih =>
    refine Prod.ext (ih _ _ (fun i A h => eq (i + 1) A h)) ?_
    exact eq 0 B rfl

theorem rename_wk_proof {Γ : VCtx τ} (B : τ) (γ : Env Γ) (b : TyDen B) :
    Env.rename (SSA.Ren.wk Γ B) (γ, b) = γ :=
  env_ext _ _ (fun i _ h => Env.rename_get (SSA.Ren.wk Γ B) (γ, b) i h)

variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
  [Iterate m] [LawfulElgotMonad m]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m]
  {Γ : VCtx τ} {L K : LCtx τ} {k : Continuation (m := m) Γ L K} {σ : Nat → Region Φ}

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem Continuation.Denotes.liftVars_proof (d : k.Denotes (ε := ε) σ) (B : τ) :
    Continuation.Denotes (ε := ε) (Γ := B :: Γ) (fun γ x => k γ.1 x) (Region.liftLSubstVars σ) := by
  intro i A h
  obtain ⟨typed, den⟩ := d h
  refine ⟨typed.renameVars ((SSA.Ren.wk Γ B).lift A), ?_⟩
  have weakened := den.renameVars ((SSA.Ren.wk Γ B).lift A)
  convert weakened using 1 <;> try rfl
  funext γ
  rcases γ with ⟨⟨γ, b⟩, a⟩
  have hrename : Env.rename ((SSA.Ren.wk Γ B).lift A) ((γ, b), a) = (γ, a) :=
    (Env.rename_lift (SSA.Ren.wk Γ B) (γ, b) A a).trans
      (congrArg (fun ρ => (ρ, a)) (rename_wk_proof B γ b))
  exact congrArg (fun ρ : Env (A :: Γ) => k ρ.1 (LabelValue.inject i h ρ.2)) hrename.symm

private theorem Continuation.Denotes.liftLabel (d : k.Denotes (ε := ε) σ) (B : τ) :
    (k.liftLabels [B]).Denotes (ε := ε) (Region.liftLSubst σ) := by
  intro i A h
  cases i with
  | zero =>
    have e : B = A := Option.some.inj h
    subst A
    have hK : At (B :: K) 0 B := rfl
    refine ⟨Region.HasType.br hK (.var rfl), ?_⟩
    convert RegionDenotes.br (h := hK)
      (Denotes.var (m := m) (ε := ε) (Γ := B :: Γ) (i := 0) rfl) using 1 <;> try rfl
    funext γ
    simp [Continuation.liftLabels, LabelValue.inject]
    rfl
  | succ i =>
    have hL : At L i A := h
    obtain ⟨typed, den⟩ := d hL
    exact ⟨_, den.weakenLabels_proof B⟩

theorem Continuation.Denotes.append_proof (d : k.Denotes (ε := ε) σ) (R : LCtx τ) :
    (k.liftLabels R).Denotes (ε := ε) (Region.liftLSubstN R.length σ) := by
  induction R with
  | nil => exact d
  | cons B R ih =>
    have h : k.liftLabels (B :: R) = (k.liftLabels R).liftLabels [B] := by
      funext γ x
      cases (show TyDen B ⊕ LabelDen (R ++ L) from x) <;> rfl
    rw [h]
    exact ih.liftLabel B

theorem RegionDenotes.bound_lsubst_proof {region : Region Φ}
    {hr : Region.HasType Γ region L} {f : Env Γ → m (LabelDen L)}
    (den : RegionDenotes ε hr f) (cont : k.Denotes (ε := ε) σ) :
    ∃ ht : Region.HasType Γ (region.bindBranchArguments.lsubst σ) K,
      RegionDenotes ε ht (k.applyTo f) := by
  induction den generalizing K σ with
  | @br Γ a A ha fa L ℓ h da =>
    obtain ⟨hs, ds⟩ := cont h
    have hsyntax := Region.lsubst_bindBranchArguments_br ℓ a σ
    rw [hsyntax]
    refine ⟨.let₁ ha hs, ?_⟩
    convert RegionDenotes.let₁ da ds using 1
    funext γ
    simp [Continuation.applyTo]
  | case de dl dr ihl ihr =>
    obtain ⟨hl, dl'⟩ := ihl (cont.liftVars_proof _)
    obtain ⟨hr, dr'⟩ := ihr (cont.liftVars_proof _)
    refine ⟨.case (by assumption) hl hr, ?_⟩
    convert RegionDenotes.case de dl' dr' using 1 <;> try rfl
    funext γ
    simp only [Continuation.applyTo, bind_assoc]
    apply bind_congr
    intro e
    cases TypeModel.coprodEquiv _ _ e <;> rfl
  | let₁ da db ih =>
    obtain ⟨ht, dt⟩ := ih (cont.liftVars_proof _)
    refine ⟨.let₁ (by assumption) ht, ?_⟩
    convert RegionDenotes.let₁ da dt using 1 <;> try rfl
    funext γ
    simp [Continuation.applyTo, bind_assoc]
  | let₂ da db ih =>
    obtain ⟨ht, dt⟩ := ih ((cont.liftVars_proof _).liftVars_proof _)
    refine ⟨.let₂ (by assumption) ht, ?_⟩
    convert RegionDenotes.let₂ da dt using 1 <;> try rfl
    funext γ
    simp [Continuation.applyTo, bind_assoc]
  | @cfgZero Γ L entry R blocks he hb fe de ihe =>
    obtain ⟨he', de'⟩ := ihe cont
    exact ⟨_, RegionDenotes.cfgZero (R := R) (L := K) he' (fun i => Fin.elim0 i) de'⟩
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
    let lifted := k.liftLabels (List.ofFn R)
    have cont' : lifted.Denotes (ε := ε) (Region.liftLSubstN (n + 1) σ) := by
      simpa only [List.length_ofFn] using cont.append_proof (List.ofFn R)
    obtain ⟨he', de'⟩ := ihe cont'
    choose hb' db' using fun i => ihb i (cont'.liftVars_proof (R i))
    let collective' : Env Γ × FiniteLabelDen R → m (LabelDen (List.ofFn R ++ K)) :=
      fun p => collective p >>= lifted p.1
    have dc' : CollectiveDenotes Γ R K (fun i γ => fb i γ >>= lifted γ.1) collective' :=
      ⟨fun i γ a => by change (collective _ >>= _) = _; rw [dc.restrict]⟩
    refine ⟨.cfg R he' hb', ?_⟩
    rw [← cfgDenotation_continuation_proof k fe collective]
    exact RegionDenotes.cfg he' hb' de' db' dc'

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem continuation_exists_proof (hσ : Region.LSubst.HasType Γ L K σ) :
    ∃ k : Continuation (m := m) Γ L K, k.Denotes (ε := ε) σ := by
  induction L generalizing σ with
  | nil =>
    exact ⟨fun _ x => x.elim, fun _ _ h => by simp [At] at h⟩
  | cons B L ih =>
    obtain ⟨head, dh⟩ := regionDenotes_exists (m := m) (ε := ε) (hσ (ℓ := 0) (A := B) rfl)
    obtain ⟨tail, dt⟩ := ih (σ := fun i => σ (i + 1)) (fun _ _ h => hσ h)
    let f : Continuation (m := m) Γ (B :: L) K :=
      fun γ x => match x with
        | .inl b => head (γ, b)
        | .inr y => tail γ y
    refine ⟨f, ?_⟩
    intro i A h
    cases i with
    | zero =>
      have e : B = A := Option.some.inj h
      subst A
      exact ⟨_, dh⟩
    | succ i => exact dt (show At L i A from h)

theorem continuation_comp_proof {H : LCtx τ} {υ : Nat → Region Φ}
    {after : Continuation (m := m) Γ K H}
    (first : k.Denotes (ε := ε) σ) (second : after.Denotes (ε := ε) υ) :
    (k.comp after).Denotes (ε := ε) (Region.boundCompLSubst σ υ) := by
  intro i A h
  obtain ⟨_, d⟩ := first h
  exact d.bound_lsubst_proof (second.liftVars_proof A)

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic
