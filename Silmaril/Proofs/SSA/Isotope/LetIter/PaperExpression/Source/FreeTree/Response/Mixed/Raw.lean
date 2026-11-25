module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Bind.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.RawArms.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Thms

/-! # Original-bound normalization and reflection for raw mixed request trees -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv HasTypeEffect)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature treeSource endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Proofs

universe u r

private theorem weaken_case_arm {Ω : Type u} (l : Expr Ω) :
    l.wk1.wk (Expr.liftWk (Expr.liftWk Nat.succ)) = l.wk1.wk1 := by
  let ρ := Expr.liftWk Nat.succ
  let ξ := Expr.liftWk ρ
  change (l.wk ρ).wk ξ = (l.wk ρ).wk ρ
  rw [Expr.wk_eq_subst (l.wk ρ) ξ, Expr.wk_eq_subst (l.wk ρ) ρ]
  simp only [Expr.subst_wk]
  congr 1
  funext i
  cases i <;> rfl

private theorem case_let {τ Ω : Type u} {ε : Type r}
    [TypeFormers τ] [HasTy Ω τ] [HasEff Ω ε] [SemilatticeSup ε] [OrderBot ε]
    {Γ : EffectCtx τ ε} {X A B C : τ} {e : ε} {p s l r : Expr Ω}
    (hp : Wf Γ p X e) (hs : Wf ((X, ⊥) :: Γ) s (coprod A B) e)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e)
    (hwl : Wf ((A, ⊥) :: (X, ⊥) :: Γ) l.wk1 C e)
    (hwr : Wf ((B, ⊥) :: (X, ⊥) :: Γ) r.wk1 C e) :
    Eqv Γ C e (.case (.let₁ p s) l r) (.let₁ p (.case s l.wk1 r.wk1)) := by
  have hrename : (Case.onHead l r).wk1 = Case.onHead l.wk1 r.wk1 := by
    change Expr.case (.var 0) (l.wk1.wk (Expr.liftWk (Expr.liftWk Nat.succ)))
      (r.wk1.wk (Expr.liftWk (Expr.liftWk Nat.succ))) =
      .case (.var 0) l.wk1.wk1 r.wk1.wk1
    rw [weaken_case_arm l, weaken_case_arm r]
  have hk := Case.source_wf hl hr
  have hk' := Case.source_wf hwl hwr
  have hcase : Eqv Γ C e (.case (.let₁ p s) l r) (.let₁ (.let₁ p s) (Case.onHead l r)) :=
    .step (.rewrite (.case (.let₁ hp hs) hl hr) (.let₁ (.let₁ hp hs) hk) (.case_bind _ _ _))
  have hassoc : Eqv Γ C e (.let₁ (.let₁ p s) (Case.onHead l r))
      (.let₁ p (.let₁ s (Case.onHead l.wk1 r.wk1))) := by
    rw [← hrename]
    exact .step (.rewrite (.let₁ (.let₁ hp hs) hk) (.let₁ hp (.let₁ hs (hrename.symm ▸ hk')))
      (.let1_let1 _ _ _))
  have hcase' : Eqv ((X, ⊥) :: Γ) C e (.case s l.wk1 r.wk1)
      (.let₁ s (Case.onHead l.wk1 r.wk1)) :=
    .step (.rewrite (.case hs hwl hwr) (.let₁ hs hk') (.case_bind _ _ _))
  exact hcase.trans (hassoc.trans (.let1 (.refl hp) hcase'.symm))

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}
  {n : Nat} {slots : Fin n → α}

private theorem input_at_arity {m k : Nat} (as : Fin m → α) (h : m = k) :
    input m as = input k (fun i => as (i.cast h.symm)) := by
  cases h
  rfl

private theorem tuple_at_arity {m k : Nat} {as : Fin m → α} (h : m = k)
    (xs : (i : Fin k) → Tree S slots (as (i.cast h.symm))) :
    sourceTuple m (fun i => treeSource (Ψ := Ψ) S (Flatten.argsAtArity S h xs i)) =
      sourceTuple k (fun i => treeSource S (xs i)) := by
  cases h
  rfl

private theorem unary_tuple {g : Ψ} (h : T.arity g = 1) :
    sourceTuple (T.arity g) (fun i => treeSource S (unaryVarArgs S T (slots := slots) h i)) =
      (.pair (.var 0) .unit : Expr (Φ ⊕ Ψ)) := by
  simp only [unaryVarArgs, tuple_at_arity S]
  rfl

variable {ε : Type r} [HasEff Φ ε]

section Typed

variable [Bot ε]

private theorem pure_at_arity {m k : Nat} {as : Fin m → α} (h : m = k)
    (xs : (i : Fin k) → Tree S slots (as (i.cast h.symm)))
    (hp : ∀ i, DeclaredPure (ε := ε) S (xs i)) :
    ∀ i, DeclaredPure (ε := ε) S (Flatten.argsAtArity S h xs i) := by
  cases h
  exact hp

private theorem unary_pure {g : Ψ} (h : T.arity g = 1) :
    ∀ i, DeclaredPure (ε := ε) S (unaryVarArgs S T (slots := slots) h i) := by
  apply pure_at_arity S
  intro i
  exact Fin.cases trivial (fun j => j.elim0) i

end Typed

variable [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]

public theorem compile_typed (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    Mixed.Program.WellTyped S T e (Program.compile (ε := ε) S T p) := by
  induction p with
  | straight p =>
    exact (ofSequence_wellTyped S T e _).mpr (Flatten.compile_typed S e p hp)
  | let1 p q ih =>
    exact bindPrefix_typed S T e _ _ (Flatten.compile_typed S e p hp.1) (ih hp.2)
  | sum g args l r ihl ihr => exact ⟨hp.1, hp.2.1, ihl hp.2.2.1, ihr hp.2.2.2⟩
  | sumUnary g h p l r ihl ihr =>
    exact bindPrefix_typed S T e _ _ (Flatten.compile_typed S e p hp.1)
      ⟨unary_pure S T h, hp.2.1, weakenUnder_typed S T e _ (ihl hp.2.2.1) _,
        weakenUnder_typed S T e _ (ihr hp.2.2.2) _⟩

variable {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

private theorem unary_source_eqv (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ss i))
    (e : ε) {g : Ψ} (h : T.arity g = 1) (hg : instrEff g ≤ e)
    (p : Flatten.Program S ss (unarySort T h)) (hp : Flatten.Program.WellTyped S e p)
    (l : Mixed.Program S T c (extendSorts (T.left g) ss))
    (r : Mixed.Program S T c (extendSorts (T.right g) ss))
    (hl : Mixed.Program.WellTyped S T e l) (hr : Mixed.Program.WellTyped S T e r)
    {left right : Expr (Φ ⊕ Ψ)}
    (el₀ : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      Eqv ((Ty.base (T.left g), ⊥) :: Γ) (.base c) e left l.source)
    (er₀ : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      Eqv ((Ty.base (T.right g), ⊥) :: Γ) (.base c) e right r.source) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.base c) e
      (.case (.op (.inr g) (.pair (p.source.mapInstr Sum.inl) .unit)) left right)
      (bindPrefix S T (Flatten.compile (ε := ε) S p)
        (.sum g (unaryVarArgs S T h) (weakenUnder S T (unarySort T h) l)
          (weakenUnder S T (unarySort T h) r))).source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  let x := unarySort T h
  let Δ := (Ty.base x, (⊥ : ε)) :: Γ
  let args := unaryVarArgs S T (slots := ss) h
  let l' := weakenUnder S T x l
  let r' := weakenUnder S T x r
  let body : Mixed.Program S T c (extendSorts x ss) := .sum g args l' r'
  have hlt := weakenUnder_typed S T e l hl x
  have hrt := weakenUnder_typed S T e r hr x
  have hbody : Mixed.Program.WellTyped S T e body := ⟨unary_pure S T h, hg, hlt, hrt⟩
  have hΔ := pure_extended hΓ x
  have hsΔ := slots_extended (a := x) hslots
  have hlwf := Mixed.source_wf S T (pure_extended hΓ (T.left g)) (slots_extended hslots) e l hl
  have hrwf := Mixed.source_wf S T (pure_extended hΓ (T.right g)) (slots_extended hslots) e r hr
  have hwl := Mixed.source_wf S T (pure_extended hΔ (T.left g)) (slots_extended hsΔ) e l' hlt
  have hwr := Mixed.source_wf S T (pure_extended hΔ (T.right g)) (slots_extended hsΔ) e r' hrt
  have el : l'.source = l.source.wk1 := weakenUnder_source S T l x
  have er : r'.source = r.source.wk1 := weakenUnder_source S T r x
  have ep := RawArms.arm_compile_eqv S T hΓ hslots e p hp
  have hpwf := ep.endpoints_wf.1
  have hin : instrSrc (Sum.inr g : Φ ⊕ Ψ) = product (Ty.base x) unit :=
    input_at_arity (T.arg g) h
  have hv : Wf Δ (.pair (.var 0) .unit : Expr (Φ ⊕ Ψ)) (product (Ty.base x) unit) e :=
    .pair (.var 0 bot_le) (.unit _ _)
  have hop := (Eqv.op (f := (Sum.inr g : Φ ⊕ Ψ)) hg
      (hin.symm ▸ CallByValue.pair_unit_bind hpwf)).trans
    (CallByValue.op_let (f := (Sum.inr g : Φ ⊕ Ψ)) hg hpwf (hin.symm ▸ hv))
  have hs : Wf Δ (.op (Sum.inr g : Φ ⊕ Ψ) (.pair (.var 0) .unit)) (SumCall.result T g) e :=
    .op (f := (Sum.inr g : Φ ⊕ Ψ)) hg (hin.symm ▸ hv)
  have hb : body.source = .case (.op (.inr g) (.pair (.var 0) .unit)) l.source.wk1 r.source.wk1 := by
    simp only [body, Mixed.Program.source, args, unary_tuple S T, el, er]
  have hprefix := bindPrefix_eqv S T hΓ hslots e _ body (Flatten.compile_typed S e p hp) hbody
  have hc := case_let hpwf hs hlwf hrwf (el ▸ hwl) (er ▸ hwr)
  rw [← hb] at hc
  exact (Eqv.case hop el₀ er₀).trans (hc.trans
    ((Eqv.let1 ep (.refl (Mixed.source_wf S T hΔ hsΔ e body hbody))).trans hprefix))

private theorem compile_eqv_aux (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots (i.cast hlen))) →
        Eqv Γ (.base c) e p.source (Program.compile (ε := ε) S T p).source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction p with
  | @straight size ambient p =>
    intro Γ hlen hΓ hs
    subst size
    exact RawArms.arm_compile_eqv S T hΓ hs e p hp
  | @let1 size ambient a p q ih =>
    intro Γ hlen hΓ hs
    subst size
    exact (Eqv.let1 (RawArms.arm_compile_eqv S T hΓ hs e p hp.1)
      (ih hp.2 rfl (pure_extended hΓ a) (slots_extended hs))).trans
        (bindPrefix_eqv S T hΓ hs e _ _ (Flatten.compile_typed S e p hp.1) (compile_typed S T e q hp.2))
  | @sum size ambient g args l r ihl ihr =>
    intro Γ hlen hΓ hs
    subst size
    exact .case (.refl (sum_request_wf S T hΓ hs args hp.1 hp.2.1))
      (ihl hp.2.2.1 rfl (pure_extended hΓ (T.left g)) (slots_extended hs))
      (ihr hp.2.2.2 rfl (pure_extended hΓ (T.right g)) (slots_extended hs))
  | @sumUnary size ambient g h p l r ihl ihr =>
    intro Γ hlen hΓ hs
    subst size
    have el := ihl hp.2.2.1 rfl (pure_extended hΓ (T.left g)) (slots_extended hs)
    have er := ihr hp.2.2.2 rfl (pure_extended hΓ (T.right g)) (slots_extended hs)
    exact unary_source_eqv S T hΓ hs e h hp.2.1 p hp.1 _ _
      (compile_typed S T e l hp.2.2.1) (compile_typed S T e r hp.2.2.2) el er

public theorem compile_eqv (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ss i))
    (e : ε) (p : Program S T c ss) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.base c) e p.source (Program.compile (ε := ε) S T p).source :=
  compile_eqv_aux S T e p hp rfl hΓ hslots

variable [EffectIteration ε]

public theorem compile_native (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ss i))
    (e : ε) (p : Program S T c ss) (hp : Program.WellTyped S T e p)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : p.source.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    HasTypeEffect Γ₀ Γ.toBoundCtx t (.base c) e ∧
    HasTypeEffect Γ₀ Γ.toBoundCtx (Program.compile (ε := ε) S T p).native (.base c) e ∧
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t (Program.compile (ε := ε) S T p).native (.base c) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have he := compile_eqv S T hΓ hslots e p hp
  exact Eqv.toLetIter_at_bound ⟨_, he.endpoints_wf.1⟩ ⟨_, he.endpoints_wf.2⟩ he ht (Mixed.lowers S T _)

variable [DecidableEq α]

public theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (p q : Program S T c ss) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (hs : q.source.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s (.base c) ↔ Eqv Γ (.base c) e p.source q.source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  refine ⟨fun hn => ?_, fun he => he.toLetIter ht hs⟩
  have ep := compile_eqv S T hΓ hslots e p hp
  have eq := compile_eqv S T hΓ hslots e q hq
  have np := ep.toLetIter ht (Mixed.lowers S T _)
  have nq := eq.toLetIter hs (Mixed.lowers S T _)
  have hm := (Mixed.endpoint_reflection S T visible hΓ hslots e _ _
    (compile_typed S T e p hp) (compile_typed S T e q hq)).mp (np.symm.trans (hn.trans nq))
  exact ep.trans (hm.trans eq.symm)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Proofs
