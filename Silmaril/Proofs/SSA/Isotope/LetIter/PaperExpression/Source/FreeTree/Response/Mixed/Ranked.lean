module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Thms

/-! # Ranked native unfolding and fixed-bound reflection after expansion -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Scoped.Proofs

universe u v v' r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {State : ∀ {n : Nat}, (Fin n → α) → Type v}
  (rank : ∀ {n : Nat} {ss : Fin n → α}, State ss → Nat)
  {c : α} {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

omit [EffectIteration ε] in
private theorem step_expand_typed {k n : Nat} {ss : Fin n → α} (e : ε) (p : Step S T (@rank) c k ss)
    (hp : Step.WellTyped S T (@rank) e p)
    (next : ∀ {m : Nat} (slots : Fin m → α) (j : State slots), rank j < k → Mixed.Program S T c slots)
    (hn : ∀ {m : Nat} (slots : Fin m → α) (j : State slots) (hj : rank j < k),
      Mixed.Program.WellTyped S T e (next slots j hj)) :
    Mixed.Program.WellTyped S T e (Step.expand (ε := ε) S T (@rank) next p) := by
  induction p with
  | done p => exact Raw.compile_typed S T e p hp
  | again j hj => exact hn _ j hj
  | atom f args next ih => exact ⟨hp.1, hp.2.1, hp.2.2.1, ih hp.2.2.2⟩
  | sum g args left right ihl ihr => exact ⟨hp.1, hp.2.1, ihl hp.2.2.1, ihr hp.2.2.2⟩

public theorem expand_typed (sys : System S T (@rank) c) {n : Nat} (ss : Fin n → α) (i : State ss) (e : ε)
    (h : System.Checked S T (@rank) sys e) :
    Mixed.Program.WellTyped S T e (System.expand (ε := ε) S T (@rank) sys ss i) := by
  generalize hk : rank i = k
  induction k using Nat.strongRecOn generalizing n with
  | ind k ih =>
    rw [System.expand]
    exact step_expand_typed S T (@rank) e _ (h.step_typed ss i) _
      (fun slots j hj => ih (rank j) (hk ▸ hj) slots j rfl)

private theorem expanded_native_typing {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hs : ∀ j, (Γ.get j).1 = .base (ss j)) (e : ε)
    (p : Mixed.Program S T c ss) (hp : Mixed.Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    HasTypeEffect Γ₀ Γ.toBoundCtx p.native (.base c) e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  obtain ⟨t, ht, htyped⟩ := (Mixed.source_wf S T hΓ hs e p hp).toLetIter
  exact (Option.some.inj (ht.symm.trans (Mixed.lowers S T p))) ▸ htyped

private theorem step_expansion {k n : Nat} {ss : Fin n → α} (e : ε) (p : Step S T (@rank) c k ss)
    (hp : Step.WellTyped S T (@rank) e p)
    (old : ∀ {m : Nat}, (ss : Fin m → α) → State ss → Tm Empty (Φ ⊕ Ψ) m)
    (next : ∀ {m : Nat} (slots : Fin m → α) (j : State slots), rank j < k → Mixed.Program S T c slots)
    (hn : ∀ {m : Nat} (slots : Fin m → α) (j : State slots) (hj : rank j < k),
      Mixed.Program.WellTyped S T e (next slots j hj))
    (he : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      ∀ {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α},
        Γ.Pure → (∀ i, (Γ.get i).1 = .base (slots i)) → ∀ (j : State slots) (hj : rank j < k),
        AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (old slots j) (next slots j hj).native (.base c)) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (ss (i.cast hlen))) →
      AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (hlen.symm ▸ Step.native (ε := ε) S T (@rank) old p)
        (hlen.symm ▸ (Step.expand (ε := ε) S T (@rank) next p).native) (.base c) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction p with
  | @done size ambient p =>
    intro Γ hlen hΓ hs
    subst size
    exact .equiv (.refl (expanded_native_typing S T hΓ hs e _ (Raw.compile_typed S T e p hp)).1)
  | @again size ambient j hj =>
    intro Γ hlen hΓ hs
    subst size
    exact he hΓ hs j hj
  | @atom size ambient f args tail ih =>
    intro Γ hlen hΓ hs
    subst size
    have ht := (expanded_native_typing S T hΓ hs e _ (step_expand_typed S T (@rank) e _ hp next hn)).1
    have tailEq := ih hp.2.2.2 rfl (Mixed.pure_extended hΓ (S.out f)) (Mixed.slots_extended hs)
    cases ht with
    | let₁ hf _ =>
      cases hf with
      | op hf => exact .let₁ (.equiv (.refl (.op hf))) tailEq
  | @sum size ambient g args left right ihl ihr =>
    intro Γ hlen hΓ hs
    subst size
    have ht := (expanded_native_typing S T hΓ hs e _ (step_expand_typed S T (@rank) e _ hp next hn)).1
    have el := ihl hp.2.2.1 rfl (Mixed.pure_extended hΓ (T.left g)) (Mixed.slots_extended hs)
    have er := ihr hp.2.2.2 rfl (Mixed.pure_extended hΓ (T.right g)) (Mixed.slots_extended hs)
    cases ht with
    | case hg _ _ =>
      cases hg with
      | op hg => exact .case (.equiv (.refl (.op hg))) el er

private theorem expansion_eqv (sys : System S T (@rank) c) (e : ε)
    (h : System.Checked S T (@rank) sys e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α}, Γ.Pure →
      (∀ j, (Γ.get j).1 = .base (ss j)) → ∀ (i : State ss),
      AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (sys.endpoint ss i)
        (System.expand (ε := ε) S T (@rank) sys ss i).native (.base c) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  suffices aux : ∀ k {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α}, Γ.Pure →
      (∀ j, (Γ.get j).1 = .base (ss j)) → ∀ (i : State ss), rank i = k →
      AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (sys.endpoint ss i)
        (System.expand (ε := ε) S T (@rank) sys ss i).native (.base c) from
    fun {_ _} hΓ hs i => aux (rank i) hΓ hs i rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro Γ ss hΓ hs i hk
    rw [System.expand]
    exact (h.unfold hΓ hs i).trans (step_expansion S T (@rank) e _ (h.step_typed ss i)
      sys.endpoint (fun slots j _ => System.expand (ε := ε) S T (@rank) sys slots j)
      (fun slots j _ => expand_typed S T (@rank) sys slots j e h)
      (fun hΓ' hs' j hj => ih (rank j) (hk ▸ hj) hΓ' hs' j rfl) rfl hΓ hs)

public theorem expand_native (sys : System S T (@rank) c) (e : ε)
    (h : System.Checked S T (@rank) sys e)
    {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} (i : State ss) (hΓ : Γ.Pure)
    (hs : ∀ j, (Γ.get j).1 = .base (ss j)) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    HasTypeEffect Γ₀ Γ.toBoundCtx (sys.endpoint ss i) (.base c) e ∧
      HasTypeEffect Γ₀ Γ.toBoundCtx (System.expand (ε := ε) S T (@rank) sys ss i).native (.base c) e ∧
      AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (sys.endpoint ss i)
        (System.expand (ε := ε) S T (@rank) sys ss i).native (.base c) :=
  ⟨h.endpoint_typed hΓ hs i, expanded_native_typing S T hΓ hs e _ (expand_typed S T (@rank) sys ss i e h),
    expansion_eqv S T (@rank) sys e h hΓ hs i⟩

variable [DecidableEq α]

public theorem raw_endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (sys : System S T (@rank) c) (e : ε) (h : System.Checked S T (@rank) sys e)
    {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} (i : State ss) (hΓ : Γ.Pure)
    (hs : ∀ j, (Γ.get j).1 = .base (ss j))
    (q : Raw.Program S T c ss) (hq : Raw.Program.WellTyped S T e q)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : q.source.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (sys.endpoint ss i) t (.base c) ↔
      Eqv Γ (.base c) e (System.expand (ε := ε) S T (@rank) sys ss i).source q.source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have hex := expansion_eqv S T (@rank) sys e h hΓ hs i
  refine ⟨fun he => ?_, fun he => hex.trans (he.toLetIter (Mixed.lowers S T _) ht)⟩
  have hq' := Raw.compile_native S T hΓ hs e q hq ht
  have hr := (Mixed.endpoint_reflection S T visible hΓ hs e _ _
    (expand_typed S T (@rank) sys ss i e h) (Raw.compile_typed S T e q hq)).mp
    (hex.symm.trans (he.trans hq'.2.2))
  exact hr.trans (Raw.compile_eqv S T hΓ hs e q hq).symm


public theorem endpoint_reflection {State' : ∀ {n : Nat}, (Fin n → α) → Type v'}
    (rank' : ∀ {n : Nat} {ss : Fin n → α}, State' ss → Nat)
    (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (e : ε)
    (sys : System S T (@rank) c) (h : System.Checked S T (@rank) sys e)
    (sys' : System S T (@rank') c) (h' : System.Checked S T (@rank') sys' e)
    {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} (i : State ss) (i' : State' ss) (hΓ : Γ.Pure)
    (hs : ∀ j, (Γ.get j).1 = .base (ss j)) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (sys.endpoint ss i) (sys'.endpoint ss i') (.base c) ↔
      Eqv Γ (.base c) e (System.expand (ε := ε) S T (@rank) sys ss i).source
        (System.expand (ε := ε) S T (@rank') sys' ss i').source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have hex := expansion_eqv S T (@rank) sys e h hΓ hs i
  have hex' := expansion_eqv S T (@rank') sys' e h' hΓ hs i'
  apply Iff.trans ?_ (Mixed.endpoint_reflection S T visible hΓ hs e _ _
    (expand_typed S T (@rank) sys ss i e h) (expand_typed S T (@rank') sys' ss i' e h'))
  exact ⟨fun he => hex.symm.trans (he.trans hex'), fun he => hex.trans (he.trans hex'.symm)⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Scoped.Proofs
