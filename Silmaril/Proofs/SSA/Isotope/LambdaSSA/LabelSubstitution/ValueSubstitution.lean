module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Soundness

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Elgot Silmaril.Isotope.LetIter.ProofRelevant.Semantics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {m : Type v → Type v} [Monad m]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m]

/-- The images of a pure variable substitution implement environment reindexing. -/
private def ValueSubstDenotes {Γ Δ : VCtx τ}
    (θ : Nat → Tm Φ) (pull : Env Δ → Env Γ) : Prop :=
  ∀ ⦃i A⦄ (h : At Γ i A), ∃ d : Tm.HasType Δ (θ i) A,
    Denotes (m := m) ε d (fun ρ => pure (Env.get (pull ρ) i h))

private theorem ValueSubstDenotes.lift {Γ Δ : VCtx τ}
    {θ : Nat → Tm Φ} {pull : Env Δ → Env Γ}
    (hθ : ValueSubstDenotes (m := m) (ε := ε) θ pull) (B : τ) :
    ValueSubstDenotes (m := m) (ε := ε) (Γ := B :: Γ) (Δ := B :: Δ)
      (Tm.liftSubst θ) (fun ρ => (pull ρ.1, ρ.2)) := by
  intro i A h
  cases i with
  | zero =>
    have e : B = A := Option.some.inj h
    subst A
    exact ⟨_, .var (i := 0) rfl⟩
  | succ i =>
    obtain ⟨d, hd⟩ := hθ (show At Γ i A from h)
    refine ⟨d.rename (SSA.Ren.wk Δ B), ?_⟩
    convert hd.renameVars (SSA.Ren.wk Δ B) using 1 <;> try rfl
    funext p
    rcases p with ⟨ρ, b⟩
    have e := rename_wk_proof B ρ b
    exact congrArg (fun p : Env Δ => pure (Env.get (pull p) i h)) e.symm

private theorem Denotes.substValues {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    {ha : Tm.HasType Γ a A} {f : Env Γ → m (TyDen A)}
    (den : Denotes ε ha f) {Δ : VCtx τ} {θ : Nat → Tm Φ} {pull : Env Δ → Env Γ}
    (hθ : ValueSubstDenotes (m := m) (ε := ε) θ pull) :
    ∃ ht : Tm.HasType Δ (a.subst θ) A, Denotes ε ht (f ∘ pull) := by
  induction den generalizing Δ θ with
  | var h => exact hθ h
  | op _ ih =>
    obtain ⟨_, h⟩ := ih hθ
    exact ⟨_, .op h⟩
  | let₁ _ _ iha ihb =>
    obtain ⟨_, ha⟩ := iha hθ
    obtain ⟨_, hb⟩ := ihb (hθ.lift _)
    exact ⟨_, .let₁ ha hb⟩
  | pair _ _ iha ihb =>
    obtain ⟨_, ha⟩ := iha hθ
    obtain ⟨_, hb⟩ := ihb hθ
    exact ⟨_, .pair ha hb⟩
  | unit => exact ⟨_, .unit⟩
  | let₂ _ _ iha ihb =>
    obtain ⟨_, ha⟩ := iha hθ
    obtain ⟨_, hb⟩ := ihb ((hθ.lift _).lift _)
    exact ⟨_, .let₂ ha hb⟩
  | inl _ ih =>
    obtain ⟨_, h⟩ := ih hθ
    exact ⟨_, .inl h⟩
  | inr _ ih =>
    obtain ⟨_, h⟩ := ih hθ
    exact ⟨_, .inr h⟩
  | case _ _ _ ihe ihl ihr =>
    obtain ⟨_, he⟩ := ihe hθ
    obtain ⟨_, hl⟩ := ihl (hθ.lift _)
    obtain ⟨_, hr⟩ := ihr (hθ.lift _)
    exact ⟨_, .case he hl hr⟩
  | abort _ ih =>
    obtain ⟨_, h⟩ := ih hθ
    exact ⟨_, .abort h⟩

variable [Iterate m]

private theorem RegionDenotes.substValues {Γ : VCtx τ} {L : LCtx τ} {region : Region Φ}
    {hr : Region.HasType Γ region L} {f : Env Γ → m (LabelDen L)}
    (den : RegionDenotes ε hr f) {Δ : VCtx τ} {θ : Nat → Tm Φ} {pull : Env Δ → Env Γ}
    (hθ : ValueSubstDenotes (m := m) (ε := ε) θ pull) :
    ∃ ht : Region.HasType Δ (region.substVars θ) L, RegionDenotes ε ht (f ∘ pull) := by
  induction den generalizing Δ θ with
  | br d =>
    obtain ⟨_, ha⟩ := d.substValues hθ
    exact ⟨_, .br ha⟩
  | let₁ d _ ih =>
    obtain ⟨_, da⟩ := d.substValues hθ
    obtain ⟨_, db⟩ := ih (hθ.lift _)
    exact ⟨_, .let₁ da db⟩
  | let₂ d _ ih =>
    obtain ⟨_, da⟩ := d.substValues hθ
    obtain ⟨_, db⟩ := ih ((hθ.lift _).lift _)
    exact ⟨_, .let₂ da db⟩
  | case d _ _ ihl ihr =>
    obtain ⟨_, de⟩ := d.substValues hθ
    obtain ⟨_, dl⟩ := ihl (hθ.lift _)
    obtain ⟨_, dr⟩ := ihr (hθ.lift _)
    exact ⟨_, .case de dl dr⟩
  | @cfgZero Γ L entry R blocks he hb fe de ihe =>
    obtain ⟨he', de'⟩ := ihe hθ
    exact ⟨_, RegionDenotes.cfgZero (R := R) (L := L) he' (fun i => Fin.elim0 i) de'⟩
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
    obtain ⟨he', de'⟩ := ihe hθ
    choose hb' db' using fun i => ihb i (hθ.lift (R i))
    let collective' : Env Δ × FiniteLabelDen R → m (LabelDen (List.ofFn R ++ L)) :=
      fun p => collective (pull p.1, p.2)
    have dc' : CollectiveDenotes Δ R L (fun i p => fb i (pull p.1, p.2)) collective' :=
      ⟨fun i ρ a => dc.restrict i (pull ρ) a⟩
    exact ⟨_, RegionDenotes.cfg he' hb' de' db' dc'⟩

theorem RegionDenotes.substPureArgument_proof {Γ : VCtx τ} {L : LCtx τ} {region : Region Φ}
    {a : Tm Φ} {A : τ} {hr : Region.HasType (A :: Γ) region L}
    {f : Env (A :: Γ) → m (LabelDen L)} {value : Env Γ → TyDen A}
    (den : RegionDenotes ε hr f) {ha : Tm.HasType Γ a A}
    (dv : Denotes (m := m) ε ha (fun ρ => pure (value ρ))) :
    ∃ ht : Region.HasType Γ (region.substVars (Tm.singleSubst a)) L,
      RegionDenotes ε ht (fun ρ => f (ρ, value ρ)) := by
  apply den.substValues (pull := fun ρ => (ρ, value ρ))
  intro i B h
  cases i with
  | zero =>
    have e : A = B := Option.some.inj h
    subst B
    exact ⟨ha, dv⟩
  | succ i =>
    exact ⟨_, .var (i := i) h⟩

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic
