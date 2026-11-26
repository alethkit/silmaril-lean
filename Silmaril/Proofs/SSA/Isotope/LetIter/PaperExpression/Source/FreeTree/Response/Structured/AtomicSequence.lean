module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue.Thms

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression (Wf)
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Proofs

universe u r

section Observation

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {A : Ty α} {n : Nat} {slots : Fin n → α}

local notation "Prog" => Program (Φ := Φ) (ε := ε)
local notation "Val" => Value (Φ := Φ) (ε := ε)
local notation "Atoms" => Atom (Φ := Φ) (ε := ε)

public theorem lowers (p : Prog A slots) : p.source.toLetIter n = some p.native := by
  induction p with
  | ret v => exact PureValues.lowers v
  | call _ _ _ _ _ ih | callPair _ _ _ _ _ ih =>
    simp only [Program.source, Program.native, Expr.toLetIter, PureValues.lowers, ih,
      Option.bind_some, Option.map_some]

section Denotation

variable (profile : Profile (α := α) Φ ε) {m : Nat} (modelSlots : Fin m → α)
  {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i))
  (vars : (i : Fin n) → Atom (Φ := Φ) (ε := ε) modelSlots (slots i))

public theorem denote_ret (v : Val slots A) :
    (Program.ret v).denote profile modelSlots hs vars =
      ITree.ret ((toSmall (Atom (Φ := Φ) (ε := ε) modelSlots) A).symm (v.subst vars).encode) :=
  denote_value_at profile modelSlots hs v vars

private theorem valuationEnv_snoc {R : Ty α} {a : α} (ty : R = .base a) (reply : Ty.denote (Atom (Φ := Φ) (ε := ε) modelSlots) R) :
    valuationEnv (Φ := Φ) (ε := ε) (Fin.cases a slots) modelSlots (replySlots hs ty)
      (Fin.cases (motive := fun i => (Atom (Φ := Φ) (ε := ε) modelSlots) (Fin.cases a slots i))
        (cast (congrArg (Ty.denote (Atom (Φ := Φ) (ε := ε) modelSlots)) ty) reply) vars) =
      (valuationEnv (Φ := Φ) (ε := ε) slots modelSlots hs vars).snoc ((toSmall (Atom (Φ := Φ) (ε := ε) modelSlots) R).symm reply) := by
  subst R
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
public theorem denote_call {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {a : α} (ty : (instrTrg f : Ty α) = .base a) (arg : Val slots (instrSrc f)) (next : Prog A (Fin.cases a slots)) :
    (Program.call f visible ty arg next).denote profile modelSlots hs vars =
      ITree.vis (.call f (arg.subst vars).encode) (fun reply =>
        next.denote profile modelSlots (replySlots hs ty)
          (Fin.cases (motive := fun i => (Atom (Φ := Φ) (ε := ε) modelSlots) (Fin.cases a slots i))
            (cast (congrArg (Ty.denote (Atom (Φ := Φ) (ε := ε) modelSlots)) ty) reply) vars)) := by
  unfold Program.denote
  rw [Program.derivation, denote_letOp_of_not_pure (Atoms modelSlots) (pureMaps modelSlots profile) visible,
    denote_value_at profile modelSlots hs arg vars]
  erw [pure_bind]
  rw [_root_.Equiv.apply_symm_apply]
  congr 1
  funext reply
  rw [valuationEnv_snoc modelSlots hs vars ty reply]

set_option backward.isDefEq.respectTransparency false in
public theorem denote_next_eq {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {a : α} (ty : (instrTrg f : Ty α) = .base a) (arg : Val slots (instrSrc f))
    {p q : Prog A (Fin.cases a slots)}
    (vals : (i : Fin (n + 1)) → Atom (Φ := Φ) (ε := ε) modelSlots (Fin.cases (motive := fun _ => α) a slots i))
    (h :
      let retained : (i : Fin n) → Atom (Φ := Φ) (ε := ε) modelSlots (slots i) := fun i => vals i.succ
      (Program.call f visible ty arg p).denote profile modelSlots hs retained =
        (Program.call f visible ty arg q).denote profile modelSlots hs retained) :
    p.denote profile modelSlots (replySlots hs ty) vals =
      q.denote profile modelSlots (replySlots hs ty) vals := by
  dsimp only at h
  rw [denote_call, denote_call] at h
  let reply : Ty.denote (Atoms modelSlots) (instrTrg f) :=
    cast (congrArg (Ty.denote (Atoms modelSlots)) ty.symm) (vals 0)
  have cont := ((vis_eq_iff (Atoms modelSlots)).mp h).2 reply
  have valEq :
      Fin.cases (motive := fun i => Atoms modelSlots (Fin.cases (motive := fun _ => α) a slots i))
        (cast (congrArg (Ty.denote (Atoms modelSlots)) ty) reply) (fun i => vals i.succ) = vals := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    simp [reply]
  rwa [valEq] at cont

set_option backward.isDefEq.respectTransparency false in
private theorem denote_pair_binder {a b : α}
    {s : Tm Empty Φ n} {t : Tm Empty Φ (n + 2)} {R : Ty α}
    (ty : R = .product (.base a) (.base b))
    (arg : Derivation Φ .nil β s R)
    (body : Derivation Φ .nil ((β.snoc (.base a)).snoc (.base b)) t A)
    (ρ : BoundEnv (Ty.denote (Lifted (Atoms modelSlots))) β) :
    let V := Atoms modelSlots
    let D := Ty.denote (Lifted V)
    let M := instructions V (pureMaps modelSlots profile)
    (Derivation.let₂ (cast (congrArg (Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β s) ty) arg) body).denote
        D M (fun x => x.elim) ρ =
      arg.denote D M (fun x => x.elim) ρ >>= fun reply =>
        let p := cast (congrArg D ty) reply
        body.denote D M (fun x => x.elim) ((ρ.snoc p.1).snoc p.2) := by
  subst R
  rfl

private theorem valuationEnv_pair {a b : α} (left : Atoms modelSlots a) (right : Atoms modelSlots b) :
    let D := Ty.denote (Lifted (Atoms modelSlots))
    let ρ := valuationEnv slots modelSlots hs vars
    valuationEnv (pairSlots a b slots) modelSlots (pairReplySlots hs a b) (pairValuation left right vars) =
      (ρ.snoc (show D (.base a) from ⟨left⟩)).snoc (show D (.base b) from ⟨right⟩) := by
  intro D ρ
  let ρ' := (ρ.snoc (show D (.base a) from ⟨left⟩)).snoc (show D (.base b) from ⟨right⟩)
  let vals := valuationEnv (pairSlots a b slots) modelSlots (pairReplySlots hs a b) (pairValuation left right vars)
  change vals = ρ'
  funext i
  refine Fin.cases (motive := fun i => vals i = ρ' i) rfl (fun j => ?_) i
  exact Fin.cases (motive := fun j => vals j.succ = ρ' j.succ) rfl (fun _ => rfl) j

set_option backward.isDefEq.respectTransparency false in
public theorem denote_callPair {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {a b : α} (ty : (instrTrg f : Ty α) = .product (.base a) (.base b))
    (arg : Val slots (instrSrc f)) (next : Prog A (pairSlots a b slots)) :
    (Program.callPair f visible ty arg next).denote profile modelSlots hs vars =
      ITree.vis (.call f (arg.subst vars).encode) (fun reply =>
        let p := cast (congrArg (Ty.denote (Atoms modelSlots)) ty) reply
        next.denote profile modelSlots (pairReplySlots hs a b)
          (pairValuation p.1 p.2 vars)) := by
  unfold Program.denote
  rw [Program.derivation, denote_pair_binder (profile := profile) (modelSlots := modelSlots) ty]
  rw [Derivation.denote, denote_value_at profile modelSlots hs arg vars]
  erw [pure_bind]
  rw [eval_bind_of_not_pure _ _ visible, _root_.Equiv.apply_symm_apply]
  congr 1
  funext reply
  have lift {R : Ty α} (h : R = .product (.base a) (.base b))
      (x : Ty.denote (Atoms modelSlots) R) :
      cast (congrArg (Ty.denote (Lifted (Atoms modelSlots))) h) ((toSmall (Atoms modelSlots) R).symm x) =
        (⟨(cast (congrArg (Ty.denote (Atoms modelSlots)) h) x).1⟩,
         ⟨(cast (congrArg (Ty.denote (Atoms modelSlots)) h) x).2⟩) := by
    subst R
    rfl
  dsimp only
  erw [lift ty reply]
  exact congrArg _ (valuationEnv_pair modelSlots hs vars _ _).symm

set_option backward.isDefEq.respectTransparency false in
public theorem denote_nextPair_eq {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {a b : α} (ty : (instrTrg f : Ty α) = .product (.base a) (.base b))
    (arg : Val slots (instrSrc f)) {p q : Prog A (pairSlots a b slots)}
    (vals : (i : Fin (n + 2)) → Atoms modelSlots (pairSlots a b slots i))
    (h :
      let retained : (i : Fin n) → Atoms modelSlots (slots i) := fun i => vals i.succ.succ
      (Program.callPair f visible ty arg p).denote profile modelSlots hs retained =
        (Program.callPair f visible ty arg q).denote profile modelSlots hs retained) :
    p.denote profile modelSlots (pairReplySlots hs a b) vals =
      q.denote profile modelSlots (pairReplySlots hs a b) vals := by
  dsimp only at h
  rw [denote_callPair, denote_callPair] at h
  let V := Atoms modelSlots
  let shape := ReplyShape.pair (ReplyShape.atom a) (ReplyShape.atom b)
  let leftSort : Fin 1 → α := fun _ => a
  let rightSort : Fin 1 → α := fun _ => b
  let left : V a := vals 1
  let right : V b := vals 0
  let fields : (i : Fin (1 + 1)) → V (Fin.addCases leftSort rightSort i) :=
    Fin.addCases (motive := fun i => V (Fin.addCases leftSort rightSort i))
      (fun i => cast (congrArg V (Fin.addCases_left (motive := fun _ => α)
        (left := leftSort) (right := rightSort) i).symm) left)
      (fun i => cast (congrArg V (Fin.addCases_right (motive := fun _ => α)
        (left := leftSort) (right := rightSort) i).symm) right)
  let reply : Ty.denote V (instrTrg f) :=
    cast (congrArg (Ty.denote V) ty.symm) (shape.denote V fields)
  have shaped : shape.denote V fields = (vals 1, vals 0) := rfl
  have cont := ((vis_eq_iff V).mp h).2 reply
  dsimp only at cont
  have replyEq : cast (congrArg (Ty.denote V) ty) reply = (vals 1, vals 0) := by
    simpa [reply] using shaped
  rw [replyEq] at cont
  have valuation : pairValuation (vals 1) (vals 0) (fun i => vals i.succ.succ) = vals := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases (motive := fun j =>
      pairValuation (vals 1) (vals 0) (fun i => vals i.succ.succ) j.succ = vals j.succ)
      rfl (fun _ => rfl) j
  rwa [valuation] at cont

end Denotation

variable (profile : Profile (α := α) Φ ε)

set_option backward.isDefEq.respectTransparency false in
public theorem eq_of_denote_eq {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i))
    {p q : Prog A slots}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α) (vars : (i : Fin n) → Atoms modelSlots (slots i)),
      p.denote profile modelSlots hs vars = q.denote profile modelSlots hs vars) : p = q := by
  induction p with
  | @ret size ss v =>
    have obs := h ss Value.var
    cases q with
    | ret w =>
      rw [denote_ret, denote_ret, ITree.ret_inj, subst_var, subst_var] at obs
      exact congrArg Program.ret (encode_injective ((toSmall (Atoms ss) A).symm.injective obs))
    | call g vG ty args next =>
      rw [denote_ret, denote_call] at obs
      exact (ITree.ret_ne_vis _ _ _ obs).elim
    | callPair g vG ty args next =>
      rw [denote_ret, denote_callPair] at obs
      exact (ITree.ret_ne_vis _ _ _ obs).elim
  | @call size ss f vF a ty args next ih =>
    have obs := h ss Value.var
    cases q with
    | ret w =>
      rw [denote_call, denote_ret] at obs
      exact (ITree.ret_ne_vis _ _ _ obs.symm).elim
    | @call _ _ g vG b ty' args' next' =>
      rw [denote_call, denote_call] at obs
      have req := request_eq_of_vis_eq (Atoms ss) obs
      have fg := congrArg Sigma.fst req
      change f = g at fg
      subst g
      have ab := Ty.base.inj (ty.symm.trans ty')
      subst b
      have eqArgs : args = args' := by
        have eqEnc := eq_of_heq (Sigma.mk.inj req).2
        exact encode_injective (by simpa only [subst_var] using eqEnc)
      subst args'
      apply congrArg (Program.call f vF ty args)
      apply ih (replySlots hs ty)
      intro m modelSlots vals
      exact denote_next_eq profile modelSlots hs vF ty args vals (h modelSlots (fun i => vals i.succ))
    | callPair g vG ty' args' next' =>
      rw [denote_call, denote_callPair] at obs
      have fg := congrArg Sigma.fst (request_eq_of_vis_eq (Atoms ss) obs)
      change f = g at fg
      subst g
      cases ty.symm.trans ty'
  | @callPair size ss f vF a b ty args next ih =>
    have obs := h ss Value.var
    cases q with
    | ret w =>
      rw [denote_callPair, denote_ret] at obs
      exact (ITree.ret_ne_vis _ _ _ obs.symm).elim
    | call g vG ty' args' next' =>
      rw [denote_callPair, denote_call] at obs
      have fg := congrArg Sigma.fst (request_eq_of_vis_eq (Atoms ss) obs)
      change f = g at fg
      subst g
      cases ty.symm.trans ty'
    | callPair g vG ty' args' next' =>
      rw [denote_callPair, denote_callPair] at obs
      have req := request_eq_of_vis_eq (Atoms ss) obs
      have fg := congrArg Sigma.fst req
      change f = g at fg
      subst g
      obtain ⟨ha, hb⟩ := Ty.product.inj (ty.symm.trans ty')
      cases Ty.base.inj ha
      cases Ty.base.inj hb
      have eqArgs : args = args' := by
        have eqEnc := eq_of_heq (Sigma.mk.inj req).2
        exact encode_injective (by simpa only [subst_var] using eqEnc)
      subst args'
      apply congrArg (Program.callPair f vF ty args)
      apply ih (pairReplySlots hs a b)
      intro m modelSlots vals
      exact denote_nextPair_eq profile modelSlots hs vF ty args vals (h modelSlots (fun i => vals i.succ.succ))

include profile in
public theorem eq_of_abortEquiv [DecidableEq α] {β : BoundCtx (Ty α) n}
    (hs : ∀ i, β.get i = .base (slots i)) {p q : Prog A slots}
    (h : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) β p.native q.native A) : p = q := by
  apply eq_of_denote_eq profile hs
  intro m modelSlots vars
  exact sound (Atoms modelSlots) (pureMaps modelSlots profile) h (p.derivation hs) (q.derivation hs)
    (valuationEnv slots modelSlots hs vars)

end Observation

section Source

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {A : Ty α} {n : Nat} {slots : Fin n → α}

private theorem sourceSlots {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {R : Ty α} {a : α} (ty : R = .base a) :
    ∀ i : Fin (Γ.length + 1), (((R, (⊥ : ε)) :: Γ).get i).1 = .base (Fin.cases a slots i) :=
  Fin.cases (motive := fun i => (((R, (⊥ : ε)) :: Γ).get i).1 = .base (Fin.cases a slots i)) ty hs

private theorem sourcePairSlots {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (a b : α) :
    ∀ i : Fin (Γ.length + 2),
      (((Ty.base b, (⊥ : ε)) :: (Ty.base a, ⊥) :: Γ).get i).1 = .base (pairSlots a b slots i) :=
  sourceSlots (Γ := (Ty.base a, ⊥) :: Γ) (sourceSlots hs (a := a) rfl) (a := b) rfl

private theorem sourcePure {Γ : EffectCtx (Ty α) ε} (hΓ : Γ.Pure) (R : Ty α) :
    EffectCtx.Pure ((R, (⊥ : ε)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((R, (⊥ : ε)) :: Γ).get j).2 = ⊥) rfl hΓ i

/-- Insert a slot below both product fields, preserving their types and effects. -/
private theorem wf_wk2 {Γ : EffectCtx (Ty α) ε} {a b x : Ty α} {e : ε} {k : Expr Φ}
    (hk : Wf ((b, ⊥) :: (a, ⊥) :: Γ) k A e) :
    Wf ((b, ⊥) :: (a, ⊥) :: (x, ⊥) :: Γ) k.wk2 A e := by
  rw [Expr.wk2, Expr.wk_eq_subst]
  apply hk.subst_typed
  intro i
  refine Fin.cases (.var 0 le_rfl) (fun j => ?_) i
  refine Fin.cases (.var 1 le_rfl) (fun k => ?_) j
  exact Wf.var (Γ := (b, ⊥) :: (a, ⊥) :: (x, ⊥) :: Γ) k.succ.succ.succ le_rfl

public theorem pairLet_bind {Γ : EffectCtx (Ty α) ε} {a b : Ty α} {e : ε}
    {s k : Expr Φ} (hs : Wf Γ s (.product a b) e)
    (hk : Wf ((b, ⊥) :: (a, ⊥) :: Γ) k A e) :
    Eqv Γ A e (.let₂ s k) (.let₁ s (.let₂ (.var 0) k.wk2)) :=
  .step (.rewrite (.let₂ hs hk)
    (.let₁ hs (.let₂ (.var 0 bot_le) (wf_wk2 hk))) (.let2_bind s k))

/-- Substituting a constructor pair for the whole reply recovers the body
under exactly the two fresh field binders. -/
public theorem pairLet_specialize {Γ : EffectCtx (Ty α) ε} {a b : Ty α} {e : ε}
    {k : Expr Φ} (hk : Wf ((b, ⊥) :: (a, ⊥) :: Γ) k A e) :
    Eqv ((b, ⊥) :: (a, ⊥) :: Γ) A e
      (ProductSplit.split 0 (.let₂ (.var 0) k.wk2)) k := by
  let Δ := (b, (⊥ : ε)) :: (a, ⊥) :: Γ
  let left : Expr Φ := .var 1
  let right : Expr Φ := .var 0
  let body := k.wk2.wk2
  have specialized : ProductSplit.split 0 (.let₂ (.var 0) k.wk2) =
      .let₂ (.pair left right) body := by
    change Expr.let₂ (.pair left right)
      (k.wk2.subst (Expr.liftSubst (Expr.liftSubst (ProductSplit.splitSubst 0)))) =
        .let₂ (.pair left right) body
    congr 1
    rw [Expr.wk2, Expr.subst_wk]
    change k.subst _ = k.wk2.wk (Expr.liftWk (Expr.liftWk Nat.succ))
    rw [Expr.wk_eq_subst k.wk2, Expr.wk2, Expr.subst_wk]
    congr 1
    funext i
    rcases i with _ | _ | i <;> rfl
  have hl : Wf Δ left a (⊥ : ε) := .var 1 le_rfl
  have hr : Wf Δ right b (⊥ : ε) := .var 0 le_rfl
  have hl' := hl.weakenEffect (show (⊥ : ε) ≤ e from bot_le)
  have hr' := hr.weakenEffect (show (⊥ : ε) ≤ e from bot_le)
  have hrwk := CallByValue.wf_wk0 hr' (a, ⊥)
  have hb : Wf ((b, ⊥) :: (a, ⊥) :: Δ) body A e :=
    wf_wk2 (x := b) (wf_wk2 (x := a) hk)
  have step : Eqv Δ A e (.let₂ (.pair left right) body) (.let₁ left (.let₁ right.wk0 body)) :=
    .step (.rewrite (.let₂ (.pair hl' hr') hb) (.let₁ hl' (.let₁ hrwk hb)) (.let2_pair _ _ _))
  have betaLeft := Eqv.step (Step.let1_beta hl (.let₁ hrwk hb))
  change Eqv Δ A e (.let₁ left (.let₁ right.wk0 body))
    (.let₁ (right.wk0.subst left.subst0) (body.subst (Expr.liftSubst left.subst0))) at betaLeft
  have hvar : right.wk0.subst left.subst0 = right := rfl
  rw [hvar] at betaLeft
  have hbody : Wf ((b, ⊥) :: Δ) (body.subst (Expr.liftSubst left.subst0)) A e := by
    apply hb.subst_typed
    intro i
    refine Fin.cases (.var 0 le_rfl) (fun j => ?_) i
    refine Fin.cases (.var 2 le_rfl) (fun k => ?_) j
    exact Wf.var (Γ := (b, ⊥) :: Δ) k.succ le_rfl
  have betaRight := Eqv.step (Step.let1_beta hr hbody)
  have substFields : (body.subst (Expr.liftSubst left.subst0)).subst right.subst0 = k := by
    dsimp only [body]
    rw [Expr.subst_comp, Expr.wk2, Expr.subst_wk, Expr.wk2, Expr.subst_wk]
    conv => rhs; rw [← Expr.subst_var k]
    congr 1
    funext i
    rcases i with _ | _ | i <;> rfl
  rw [substFields] at betaRight
  rw [specialized]
  exact step.trans (betaLeft.trans betaRight)

private theorem wf_aux (p : Program (Φ := Φ) (ε := ε) A slots) {e : ε} (hp : p.Within e) :
    ∀ {Γ : EffectCtx (Ty α) ε} (len : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots (i.cast len))) → Wf Γ p.source A e := by
  induction p with
  | @ret size _ value =>
    intro Γ len hΓ hs
    subst size
    exact (PureValues.wf value hΓ hs).weakenEffect bot_le
  | @call size ss f visible a ty arg next ih =>
    intro Γ len hΓ hs
    subst size
    exact .let₁ (.op hp.1 ((PureValues.wf arg hΓ hs).weakenEffect bot_le))
      (ih hp.2 rfl (sourcePure hΓ _) (sourceSlots hs ty))
  | @callPair size ss f visible a b ty arg next ih =>
    intro Γ len hΓ hs
    subst size
    have call := Wf.op (f := f) hp.1 ((PureValues.wf arg hΓ hs).weakenEffect bot_le)
    rw [ty] at call
    exact .let₂ call (ih hp.2 rfl (sourcePure (sourcePure hΓ _) _) (sourcePairSlots hs a b))

public theorem wf {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {e : ε}
    (p : Program (Φ := Φ) (ε := ε) A slots) (hp : p.Within e) : Wf Γ p.source A e :=
  wf_aux p hp rfl hΓ hs

end Source

section Normalize

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [PartialOrder ε] [OrderBot ε]
  (profile : Profile (α := α) Φ ε) {A : Ty α} {e : ε} {Γ : EffectCtx (Ty α) ε} {a : Expr Φ}

include profile in
public theorem normalize (h : Written A e Γ a) :
    ∀ (slots : Fin Γ.length → α), Γ.Pure →
      (∀ i, (Γ.get i).1 = .base (slots i)) →
      ∃ p : Program (Φ := Φ) (ε := ε) A slots, p.Within e ∧ Eqv Γ A e a p.source := by
  induction h with
  | ret typed leaf =>
    intro slots hΓ hs
    obtain ⟨v, hv⟩ := normalize_leaf profile typed leaf hΓ hs e
    exact ⟨.ret v, trivial, hv⟩
  | @call Γ arg k f r visible reply typed leaf bound _ ih =>
    intro slots hΓ hs
    obtain ⟨v, hv⟩ := normalize_leaf profile typed leaf hΓ hs e
    obtain ⟨next, hn, he⟩ := ih (Fin.cases r slots) (sourcePure hΓ _) (sourceSlots hs reply)
    exact ⟨.call f visible reply v next, ⟨bound, hn⟩, .let1 (.op bound hv) he⟩
  | @callPair Γ arg k f a b visible reply typed leaf bound _ ih =>
    intro slots hΓ hs
    obtain ⟨v, hv⟩ := normalize_leaf profile typed leaf hΓ hs e
    obtain ⟨next, hn, he⟩ := ih (pairSlots a b slots) (sourcePure (sourcePure hΓ _) _)
      (sourcePairSlots hs a b)
    have req := Eqv.op (f := f) bound hv
    rw [reply] at req
    exact ⟨.callPair f visible reply v next, ⟨bound, hn⟩, .let2 req he⟩
  | @callPairViaLet Γ arg k f a b visible reply typed leaf bound _ ih =>
    intro slots hΓ hs
    obtain ⟨v, hv⟩ := normalize_leaf profile typed leaf hΓ hs e
    obtain ⟨next, hn, he⟩ := ih (pairSlots a b slots) (sourcePure (sourcePure hΓ _) _)
      (sourcePairSlots hs a b)
    have req := Eqv.op (f := f) bound hv
    rw [reply] at req
    exact ⟨.callPair f visible reply v next, ⟨bound, hn⟩,
      (pairLet_bind req.endpoints_wf.1 he.endpoints_wf.1).symm.trans (.let2 req he)⟩

end Normalize

section Reflection

variable {α Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α]
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  (profile : Profile (α := α) Φ ε) {A : Ty α} {Γ : EffectCtx (Ty α) ε}
  {slots : Fin Γ.length → α}

include profile in
public theorem endpoint_reflection (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {e : ε}
    (p q : Program (Φ := Φ) (ε := ε) A slots) (hp : p.Within e) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native A ↔
      Eqv Γ A e p.source q.source := by
  refine ⟨fun h => ?_, fun h => h.toLetIter (lowers p) (lowers q)⟩
  have eq := eq_of_abortEquiv profile (fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i)) h
  subst q
  exact .refl (wf hΓ hs p hp)

include profile in
public theorem written_reflection
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {e : ε}
    {a b : Expr Φ} (ha : Written A e Γ a) (hb : Written A e Γ b)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A ↔ Eqv Γ A e a b := by
  refine ⟨fun h => ?_, fun eq => eq.toLetIter ht hs'⟩
  obtain ⟨p, hp, ep⟩ := normalize profile ha slots hΓ hs
  obtain ⟨q, _, eq⟩ := normalize profile hb slots hΓ hs
  have left := ep.toLetIter ht (lowers p)
  have right := eq.toLetIter hs' (lowers q)
  have middle := (endpoint_reflection profile hΓ hs p q hp).mp (.trans (.trans left.symm h) right)
  exact ep.trans (middle.trans eq.symm)

end Reflection

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Proofs
