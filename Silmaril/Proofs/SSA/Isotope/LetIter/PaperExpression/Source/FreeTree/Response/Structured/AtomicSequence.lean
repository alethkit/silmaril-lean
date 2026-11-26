module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
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
  | call _ _ _ _ _ ih =>
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

private theorem sourcePure {Γ : EffectCtx (Ty α) ε} (hΓ : Γ.Pure) (R : Ty α) :
    EffectCtx.Pure ((R, (⊥ : ε)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((R, (⊥ : ε)) :: Γ).get j).2 = ⊥) rfl hΓ i

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
