module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Pure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Soundness

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Elgot Silmaril.Isotope.LetIter.ProofRelevant.Semantics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {m : Type v → Type v} [Monad m] [LawfulMonad m]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m]

theorem pureTerm_denotes_proof {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    (typed : Tm.HasType Γ a A) (hp : a.Pure (⊥ : ε)) :
    ∃ value : Env Γ → TyDen A, Denotes (m := m) ε typed (fun ρ => pure (value ρ)) := by
  induction typed with
  | var h => exact ⟨_, .var h⟩
  | unit => exact ⟨_, .unit⟩
  | op ha ih =>
    next f =>
      cases hp with
      | op hf hp =>
        obtain ⟨a, da⟩ := ih hp
        refine ⟨fun ρ => denotePureInstr (m := m) f hf (a ρ), ?_⟩
        simpa only [pure_bind, InstructionModel.denote_pure f hf, denotePureInstr] using Denotes.op da
  | let₁ ha hb iha ihb =>
    cases hp with
    | let₁ hpa hpb =>
      obtain ⟨a, da⟩ := iha hpa
      obtain ⟨b, db⟩ := ihb hpb
      exact ⟨fun ρ => b (ρ, a ρ), by simpa only [pure_bind] using Denotes.let₁ da db⟩
  | pair ha hb iha ihb =>
    cases hp with
    | pair hpa hpb =>
      obtain ⟨a, da⟩ := iha hpa
      obtain ⟨b, db⟩ := ihb hpb
      refine ⟨fun ρ => (TypeModel.productEquiv _ _).symm (a ρ, b ρ), ?_⟩
      simpa only [pure_bind] using Denotes.pair da db
  | let₂ ha hb iha ihb =>
    cases hp with
    | let₂ hpa hpb =>
      obtain ⟨a, da⟩ := iha hpa
      obtain ⟨b, db⟩ := ihb hpb
      refine ⟨fun ρ => let p := TypeModel.productEquiv _ _ (a ρ); b ((ρ, p.1), p.2), ?_⟩
      simpa only [pure_bind] using Denotes.let₂ da db
  | inl ha ih =>
    cases hp with
    | inl hp =>
      obtain ⟨a, da⟩ := ih hp
      refine ⟨fun ρ => (TypeModel.coprodEquiv _ _).symm (.inl (a ρ)), ?_⟩
      simpa only [pure_bind] using Denotes.inl da
  | inr ha ih =>
    cases hp with
    | inr hp =>
      obtain ⟨a, da⟩ := ih hp
      refine ⟨fun ρ => (TypeModel.coprodEquiv _ _).symm (.inr (a ρ)), ?_⟩
      simpa only [pure_bind] using Denotes.inr da
  | case he hl hr ihe ihl ihr =>
    cases hp with
    | case hpe hpl hpr =>
      obtain ⟨e, de⟩ := ihe hpe
      obtain ⟨l, dl⟩ := ihl hpl
      obtain ⟨r, dr⟩ := ihr hpr
      refine ⟨fun ρ => match TypeModel.coprodEquiv _ _ (e ρ) with
        | .inl a => l (ρ, a) | .inr b => r (ρ, b), ?_⟩
      convert Denotes.case de dl dr using 1
      funext ρ
      rw [pure_bind]
      dsimp only
      cases TypeModel.coprodEquiv _ _ (e ρ) <;> rfl
  | abort ha ih =>
    cases hp with
    | abort hp =>
      obtain ⟨a, da⟩ := ih hp
      refine ⟨fun ρ => Empty.elim (TypeModel.emptyEquiv (a ρ)), ?_⟩
      convert Denotes.abort da using 1
      funext ρ
      exact (TypeModel.emptyEquiv (a ρ)).elim

private theorem branchValue_pure {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    (h : Tm.BranchValue Γ a A) :
    ∃ (ha : Tm.HasType Γ a A) (value : Env Γ → TyDen A),
      Denotes (m := m) ε ha (fun ρ => pure (value ρ)) := by
  induction h with
  | var h => exact ⟨_, _, .var h⟩
  | unit => exact ⟨_, _, .unit⟩
  | pair _ _ iha ihb =>
    obtain ⟨ha, a, da⟩ := iha
    obtain ⟨hb, b, db⟩ := ihb
    refine ⟨.pair ha hb, fun ρ => (TypeModel.productEquiv _ _).symm (a ρ, b ρ), ?_⟩
    simpa only [pure_bind] using Denotes.pair da db
  | inl _ ih =>
    obtain ⟨ha, a, da⟩ := ih
    refine ⟨.inl ha, fun ρ => (TypeModel.coprodEquiv _ _).symm (.inl (a ρ)), ?_⟩
    simpa only [pure_bind] using Denotes.inl da
  | inr _ ih =>
    obtain ⟨ha, a, da⟩ := ih
    refine ⟨.inr ha, fun ρ => (TypeModel.coprodEquiv _ _).symm (.inr (a ρ)), ?_⟩
    simpa only [pure_bind] using Denotes.inr da

theorem valueBranches_pure_proof {Γ : VCtx τ} {L : LCtx τ} {region : Region Φ}
    (h : Region.ValueBranches Γ region L) :
    PureBranches (m := m) ε Γ region L := by
  induction h with
  | br hℓ ha =>
    obtain ⟨_, _, dv⟩ := branchValue_pure (m := m) (ε := ε) ha
    exact .br hℓ dv
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb

variable [Iterate m] [LawfulElgotMonad m]

theorem pure_lsubst_proof {Γ : VCtx τ} {L K : LCtx τ} {region : Region Φ}
    (h : PureBranches (m := m) ε Γ region L) {σ : Nat → Region Φ}
    {k : Continuation (m := m) Γ L K} (d : k.Denotes (ε := ε) σ) :
    ∃ (hr : Region.HasType Γ region L) (hs : Region.HasType Γ (region.lsubst σ) K)
      (f : Env Γ → m (LabelDen L)), RegionDenotes ε hr f ∧ RegionDenotes ε hs (k.applyTo f) := by
  induction h generalizing K σ with
  | br hl ha =>
    obtain ⟨_, ds⟩ := d hl
    obtain ⟨hs, hsub⟩ := ds.substPureArgument_proof ha
    refine ⟨_, hs, _, RegionDenotes.br (h := hl) ha, ?_⟩
    convert hsub using 1 <;> try rfl
    funext ρ
    simp [Continuation.applyTo, pure_bind]
  | let₁ ha _ ih =>
    obtain ⟨hr, hs, _, dr, ds⟩ := ih (d.liftVars_proof _)
    let da := denote_spec (ε := ε) (m := m) ha
    refine ⟨.let₁ ha hr, .let₁ ha hs, _, RegionDenotes.let₁ da dr, ?_⟩
    convert RegionDenotes.let₁ da ds using 1 <;> try rfl
    funext ρ
    simp [Continuation.applyTo, bind_assoc]
  | let₂ ha _ ih =>
    obtain ⟨hr, hs, _, dr, ds⟩ := ih ((d.liftVars_proof _).liftVars_proof _)
    let da := denote_spec (ε := ε) (m := m) ha
    refine ⟨.let₂ ha hr, .let₂ ha hs, _, RegionDenotes.let₂ da dr, ?_⟩
    convert RegionDenotes.let₂ da ds using 1 <;> try rfl
    funext ρ
    simp [Continuation.applyTo, bind_assoc]
  | case ha _ _ ihl ihr =>
    obtain ⟨hl, hls, _, dl, dls⟩ := ihl (d.liftVars_proof _)
    obtain ⟨hr, hrs, _, dr, drs⟩ := ihr (d.liftVars_proof _)
    let da := denote_spec (ε := ε) (m := m) ha
    refine ⟨.case ha hl hr, .case ha hls hrs, _, RegionDenotes.case da dl dr, ?_⟩
    convert RegionDenotes.case da dls drs using 1 <;> try rfl
    funext ρ
    simp only [Continuation.applyTo, bind_assoc]
    apply bind_congr
    intro e
    cases TypeModel.coprodEquiv _ _ e <;> rfl
  | @cfg Γ L n R entry blocks he hb ihe ihb =>
    cases n with
    | zero =>
      obtain ⟨he, hes, _, de, des⟩ := ihe d
      exact ⟨_, _, _, RegionDenotes.cfgZero (R := R) (L := L) he (fun i => Fin.elim0 i) de,
        RegionDenotes.cfgZero (R := R) (L := K) hes (fun i => Fin.elim0 i) des⟩
    | succ n =>
      let lifted := k.liftLabels (List.ofFn R)
      have d' : lifted.Denotes (ε := ε) (Region.liftLSubstN (n + 1) σ) := by
        simpa only [List.length_ofFn] using d.append_proof (List.ofFn R)
      obtain ⟨he, hes, fe, de, des⟩ := ihe d'
      choose hb hbs fb db dbs using fun i => ihb i (d'.liftVars_proof (R i))
      obtain ⟨collective, dc⟩ := collectiveDenotes_exists_succ n Γ R L fb
      let collective' : Env Γ × FiniteLabelDen R → m (LabelDen (List.ofFn R ++ K)) :=
        fun p => collective p >>= lifted p.1
      have dc' : CollectiveDenotes Γ R K (fun i γ => fb i γ >>= lifted γ.1) collective' :=
        ⟨fun i ρ a => by change (collective _ >>= _) = _; rw [dc.restrict]⟩
      refine ⟨.cfg R he hb, .cfg R hes hbs, _, RegionDenotes.cfg he hb de db dc, ?_⟩
      rw [← cfgDenotation_continuation k fe collective]
      exact RegionDenotes.cfg hes hbs des dbs dc'

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic
