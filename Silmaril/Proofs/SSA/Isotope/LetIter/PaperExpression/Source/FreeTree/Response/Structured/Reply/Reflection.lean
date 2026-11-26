module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Observation.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection.Proofs

universe u r

public theorem shape_constructor {α Φ : Type u} {n m : Nat} {sorts : Fin n → α} {R : Ty α}
    (shape : ReplyShape sorts R) (place : Fin n → Fin m) :
    ConstructorLeaf (shape.source (Φ := Φ) place) := by
  induction shape with
  | atom => exact .var _
  | unit => exact .unit
  | pair _ _ ihL ihR => exact .pair (ihL _) (ihR _)
  | inl _ ih => exact .inl (ih place)
  | inr _ ih => exact .inr (ih place)

variable {α Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α]
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  (profile : Profile (α := α) Φ ε) {A : Ty α} {Γ : EffectCtx (Ty α) ε} {e : ε} {a b : Expr Φ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "Atoms" => Atom (Φ := Φ) (ε := ε)
local notation "D[" ss "]" => Ty.denote (Lifted (Atoms ss))

private def Agrees (profile : Profile (α := α) Φ ε) (Γ : EffectCtx (Ty α) ε)
    (A : Ty α) (a b : Expr Φ) : Prop :=
  ∀ {t s : Tm Empty Φ Γ.length}, a.toLetIter Γ.length = some t → b.toLetIter Γ.length = some s →
    ∀ (dt : Derivation Φ Γ₀ Γ.toBoundCtx t A) (ds : Derivation Φ Γ₀ Γ.toBoundCtx s A)
      {m : Nat} (model : Fin m → α) (ρ : BoundEnv D[model] Γ.toBoundCtx),
      dt.denote D[model] (instructions (Atoms model) (pureMaps model profile)) (fun z => z.elim) ρ =
        ds.denote D[model] (instructions (Atoms model) (pureMaps model profile)) (fun z => z.elim) ρ

omit [DecidableEq α] in
private theorem lower_typed (h : Wf Γ a A e) :
    ∃ t : Tm Empty Φ Γ.length, a.toLetIter Γ.length = some t ∧
      Nonempty (Derivation Φ Γ₀ Γ.toBoundCtx t A) := by
  obtain ⟨t, ht, typed⟩ := h.toLetIter
  exact ⟨t, ht, Derivation.ofHasType typed.1⟩

omit [EffectIteration ε] in
private theorem same_denote {m : Nat} (model : Fin m → α) {t : Tm Empty Φ Γ.length}
    (dt ds : Derivation Φ Γ₀ Γ.toBoundCtx t A) (ρ : BoundEnv D[model] Γ.toBoundCtx) :
    dt.denote D[model] (instructions (Atoms model) (pureMaps model profile)) (fun z => z.elim) ρ =
      ds.denote D[model] (instructions (Atoms model) (pureMaps model profile)) (fun z => z.elim) ρ :=
  sound (Atoms model) (pureMaps model profile) (.refl dt.toHasType) dt ds ρ

include profile in
private theorem arg_returns_pure {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (typed : Wf Γ a A ⊥) (leaf : ConstructorLeaf a)
    {t : Tm Empty Φ Γ.length} (ht : a.toLetIter Γ.length = some t) (d : Derivation Φ Γ₀ Γ.toBoundCtx t A)
    {m : Nat} (model : Fin m → α) (ρ : BoundEnv D[model] Γ.toBoundCtx) :
    ∃ x, d.denote D[model] (instructions (Atoms model) (pureMaps model profile)) (fun z => z.elim) ρ = pure x := by
  obtain ⟨v, eq⟩ := normalize_leaf profile typed leaf hΓ hs (⊥ : ε)
  let hslots := fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i)
  let vars (i : Fin Γ.length) : Atoms model (slots i) :=
    (cast (congrArg D[model] (hslots i)) (ρ i)).down
  have env : valuationEnv slots model hslots vars = ρ := by
    funext i
    change cast (congrArg D[model] (hslots i).symm) (cast (congrArg D[model] (hslots i)) (ρ i)) = ρ i
    simp
  have obs := sound (Atoms model) (pureMaps model profile) (eq.toLetIter ht (lowers v))
    d (v.derivation hslots) ρ
  rw [← env, denote_value_at profile model hslots v vars] at obs
  rw [env] at obs
  exact ⟨_, obs⟩

omit [HasTy Φ (Ty α)] [DecidableEq α] [HasEff Φ ε] [EffectIteration ε] in
private theorem field_context {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {n : Nat} (sorts : Fin n → α) :
    let Δ := ReplyShape.fieldCtx sorts Γ
    let extended : Fin Δ.length → α := fun i => Fin.addCases sorts slots (i.cast (ReplyShape.fieldCtx_length sorts Γ))
    Δ.Pure ∧ ∀ i, (Δ.get i).1 = .base (extended i) := by
  intro Δ extended
  have get (i : Fin Δ.length) : Δ.get i = (.base (extended i), (⊥ : ε)) := by
    refine (Fin.addCases (motive := fun j =>
      Δ.get (j.cast (ReplyShape.fieldCtx_length sorts Γ).symm) =
        (.base (Fin.addCases sorts slots j), ⊥)) ?_ ?_
      (i.cast (ReplyShape.fieldCtx_length sorts Γ)))
    · intro j
      rw [Fin.addCases_left]
      exact ReplyShape.get_fieldIndex j
    · intro j
      rw [Fin.addCases_right]
      exact (ReplyShape.get_ambientIndex (sorts := sorts) j).trans (Prod.ext (hs j) (hΓ j))
  exact ⟨fun i => congrArg Prod.snd (get i), fun i => congrArg Prod.fst (get i)⟩

include profile in
omit [EffectIteration ε] in
private theorem agrees_of_native {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (native : AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A) :
    Agrees profile Γ A a b := by
  intro t' s' ht' hs' dt ds m model ρ
  have eT := Option.some.inj (ht'.symm.trans ht)
  have eS := Option.some.inj (hs'.symm.trans hs)
  subst t'
  subst s'
  exact sound (Atoms model) (pureMaps model profile) native dt ds ρ

omit [DecidableEq α] [EffectIteration ε] in
private theorem agrees_symm (h : Agrees profile Γ A a b) : Agrees profile Γ A b a := by
  intro t s ht hs dt ds m model ρ
  exact (h hs ht ds dt model ρ).symm

private theorem agrees_of_eqv {a' b' : Expr Φ}
    (ha : Eqv Γ A e a a') (hb : Eqv Γ A e b b') (h : Agrees profile Γ A a b) :
    Agrees profile Γ A a' b' := by
  obtain ⟨t, ht, ⟨dt⟩⟩ := lower_typed ha.endpoints_wf.1
  obtain ⟨s, hs, ⟨ds⟩⟩ := lower_typed hb.endpoints_wf.1
  intro t' s' ht' hs' dt' ds' m model ρ
  let V := Atoms model
  let P := pureMaps model profile
  exact (sound V P (ha.toLetIter ht ht') dt dt' ρ).symm.trans
    ((h ht hs dt ds model ρ).trans (sound V P (hb.toLetIter hs hs') ds ds' ρ))

omit [HasTy Φ (Ty α)] [DecidableEq α] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] in
private theorem lower_letOp {f : Φ} {arg k : Expr Φ}
    {u : Tm Empty Φ Γ.length} {t : Tm Empty Φ (Γ.length + 1)}
    (hu : arg.toLetIter Γ.length = some u) (ht : k.toLetIter (Γ.length + 1) = some t) :
    (Expr.let₁ (.op f arg) k).toLetIter Γ.length = some (.let₁ (.op f u) t) := by
  simp only [Expr.toLetIter, hu, ht, Option.bind_some, Option.map_some]

omit [DecidableEq α] [EffectIteration ε] in
private theorem denote_visible {m : Nat} (model : Fin m → α) {f : Φ}
    (visible : ¬ IsPure (⊥ : ε) f)
    {u : Tm Empty Φ Γ.length} {k : Tm Empty Φ (Γ.length + 1)}
    (du : Derivation Φ Γ₀ Γ.toBoundCtx u (instrSrc f))
    (dk : Derivation Φ Γ₀ (Γ.toBoundCtx.snoc (instrTrg f)) k A)
    (ρ : BoundEnv D[model] Γ.toBoundCtx) {x : D[model] (instrSrc f)}
    (hx : du.denote D[model] (instructions (Atoms model) (pureMaps model profile)) (fun z => z.elim) ρ = pure x) :
    (Derivation.let₁ (.op (f := f) du) dk).denote D[model]
      (instructions (Atoms model) (pureMaps model profile)) (fun z => z.elim) ρ =
      ITree.vis (.call f (toSmall (Atoms model) (instrSrc f) x)) (fun reply =>
        dk.denote D[model] (instructions (Atoms model) (pureMaps model profile)) (fun z => z.elim)
          (ρ.snoc ((toSmall (Atoms model) (instrTrg f)).symm reply))) := by
  rw [denote_letOp_of_not_pure (Atoms model) (pureMaps model profile) visible, hx, pure_bind]

include profile in
private theorem call_eq_of_agrees {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    {f g : Φ} (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g) {arg arg' k l : Expr Φ}
    (ha : Wf Γ arg (instrSrc f) ⊥) (hb : Wf Γ arg' (instrSrc g) ⊥)
    (la : ConstructorLeaf arg) (lb : ConstructorLeaf arg')
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) (hl : Wf ((instrTrg g, ⊥) :: Γ) l A e)
    (obs : Agrees profile Γ A (.let₁ (.op f arg) k) (.let₁ (.op g arg') l)) :
    f = g ∧ Eqv Γ (instrSrc f) e arg arg' := by
  obtain ⟨u, hu, ⟨du⟩⟩ := lower_typed ha
  obtain ⟨v, hv, ⟨dv⟩⟩ := lower_typed hb
  obtain ⟨t, ht, ⟨dt⟩⟩ := lower_typed hk
  obtain ⟨s, hs', ⟨ds⟩⟩ := lower_typed hl
  let ρ := variableEnv (Φ := Φ) (ε := ε) slots (fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i))
  obtain ⟨x, hx⟩ := arg_returns_pure profile hΓ hs ha la hu du slots ρ
  obtain ⟨y, hy⟩ := arg_returns_pure profile hΓ hs hb lb hv dv slots ρ
  have calls := obs (lower_letOp hu ht) (lower_letOp hv hs') (.let₁ (.op du) dt) (.let₁ (.op dv) ds) slots ρ
  rw [denote_visible profile slots hf du dt ρ hx, denote_visible profile slots hg dv ds ρ hy] at calls
  have request := request_eq_of_vis_eq (Atoms slots) calls
  have opcode : f = g := congrArg Sigma.fst request
  subst g
  have value := (toSmall (Atoms slots) (instrSrc f)).injective (eq_of_heq (Sigma.mk.inj request).2)
  exact ⟨rfl, (constructor_denote_iff profile hΓ hs e ha hb la lb hu hv du dv).mp
    (hx.trans ((congrArg pure value).trans hy.symm))⟩

include profile in
private theorem leaf_ne_call {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {f : Φ}
    (hf : ¬ IsPure (⊥ : ε) f) {value arg k : Expr Φ}
    (hvalue : Wf Γ value A ⊥) (lvalue : ConstructorLeaf value)
    (harg : Wf Γ arg (instrSrc f) ⊥) (larg : ConstructorLeaf arg)
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) :
    ¬ Agrees profile Γ A value (.let₁ (.op f arg) k) := by
  intro obs
  obtain ⟨t, ht, ⟨dt⟩⟩ := lower_typed hvalue
  obtain ⟨u, hu, ⟨du⟩⟩ := lower_typed harg
  obtain ⟨s, hs', ⟨ds⟩⟩ := lower_typed hk
  let ρ := variableEnv (Φ := Φ) (ε := ε) slots (fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i))
  obtain ⟨x, hx⟩ := arg_returns_pure profile hΓ hs hvalue lvalue ht dt slots ρ
  obtain ⟨y, hy⟩ := arg_returns_pure profile hΓ hs harg larg hu du slots ρ
  have comparison := obs ht (lower_letOp hu hs') dt (.let₁ (.op du) ds) slots ρ
  rw [hx, denote_visible profile slots hf du ds ρ hy] at comparison
  exact ITree.ret_ne_vis _ _ _ comparison

include profile in
public theorem call_request_inversion {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    {f g : Φ} (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g) {arg arg' k l : Expr Φ}
    (ha : Wf Γ arg (instrSrc f) ⊥) (hb : Wf Γ arg' (instrSrc g) ⊥)
    (la : ConstructorLeaf arg) (lb : ConstructorLeaf arg')
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) (hl : Wf ((instrTrg g, ⊥) :: Γ) l A e)
    {t s : Tm Empty Φ Γ.length}
    (ht : (Expr.let₁ (.op f arg) k).toLetIter Γ.length = some t)
    (hs' : (Expr.let₁ (.op g arg') l).toLetIter Γ.length = some s)
    (native : AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A) :
    f = g ∧ Eqv Γ (instrSrc f) e arg arg' :=
  call_eq_of_agrees profile hΓ hs hf hg ha hb la lb hk hl (agrees_of_native profile ht hs' native)

set_option backward.isDefEq.respectTransparency false in
private theorem agrees_child {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {arg k l : Expr Φ}
    (typed : Wf Γ arg (instrSrc f) ⊥) (leaf : ConstructorLeaf arg)
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) (hl : Wf ((instrTrg f, ⊥) :: Γ) l A e)
    (h : Agrees profile Γ A (.let₁ (.op f arg) k) (.let₁ (.op f arg) l))
    {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts (instrTrg f)) :
    Agrees profile (ReplyShape.fieldCtx sorts Γ) A (shape.specialize Γ k) (shape.specialize Γ l) := by
  intro t s ht hs' dt ds m model ξ
  obtain ⟨u, hu, ⟨du⟩⟩ := lower_typed typed
  obtain ⟨k', hk', ⟨dk⟩⟩ := lower_typed hk
  obtain ⟨l', hl', ⟨dl⟩⟩ := lower_typed hl
  have ht' := shape.specialize_lowers hk'
  have hsEnd := shape.specialize_lowers hl'
  have eT := Option.some.inj (ht.symm.trans ht')
  have eS := Option.some.inj (hs'.symm.trans hsEnd)
  subst t
  subst s
  let V := Atoms model
  let P := pureMaps model profile
  let ρ : BoundEnv D[model] Γ.toBoundCtx := fun i =>
    cast (congrArg D[model] (ReplyShape.get_ambientType (sorts := sorts) i)) (ξ (ReplyShape.ambientIndex sorts Γ i))
  let fields (i : Fin n) : V (sorts i) :=
    (cast (congrArg D[model] (ReplyShape.get_fieldType i)) (ξ (ReplyShape.fieldIndex sorts Γ i))).down
  have hfields (i : Fin n) : HEq (ξ (ReplyShape.fieldIndex sorts Γ i)) (ULift.up.{u+1} (fields i)) :=
    (cast_heq (congrArg D[model] (ReplyShape.get_fieldType i)) _).symm
  have hambient (i : Fin Γ.length) : HEq (ξ (ReplyShape.ambientIndex sorts Γ i)) (ρ i) :=
    (cast_heq (congrArg D[model] (ReplyShape.get_ambientType (sorts := sorts) i)) _).symm
  obtain ⟨x, hx⟩ := arg_returns_pure profile hΓ hs typed leaf hu du model ρ
  have head := h (lower_letOp hu hk') (lower_letOp hu hl')
    (.let₁ (.op du) dk) (.let₁ (.op du) dl) model ρ
  have replies := ReplyShape.specialize_of_letOp_denote_eq V P visible du dk dl ρ hx head shape fields ξ hfields hambient
  exact (same_denote profile model dt _ ξ).trans (replies.trans (same_denote profile model _ ds ξ))

include profile in
private theorem eqv_of_agrees (code : Shared A e Γ a b) (hΓ : Γ.Pure)
    (h : Agrees profile Γ A a b) :
    ∀ (slots : Fin Γ.length → α), (∀ i, (Γ.get i).1 = .base (slots i)) → Eqv Γ A e a b := by
  induction code with
  | leaf ha hb la lb =>
    intro slots hs
    obtain ⟨t, ht, ⟨dt⟩⟩ := lower_typed ha
    obtain ⟨s, hs', ⟨ds⟩⟩ := lower_typed hb
    exact (constructor_denote_iff profile hΓ hs _ ha hb la lb ht hs' dt ds).mp
      (h ht hs' dt ds slots (variableEnv slots (fun i => (EffectCtx.get_toBoundCtx _ i).trans (hs i))))
  | @call Γ f arg k l visible bound typed leaf hk hl _ ih =>
    intro slots hs
    apply ReplyShape.eqv_let_of_specializations (fun i => ⟨slots i, hs i⟩) hΓ
      (.op bound (typed.weakenEffect bot_le)) hk hl
    intro n sorts shape
    have contexts := field_context hΓ hs sorts
    exact ih shape contexts.1 (agrees_child profile visible hΓ hs typed leaf hk hl h shape) _ contexts.2
  | normalize ha hb _ ih =>
    intro slots hs
    exact ha.trans ((ih hΓ (agrees_of_eqv profile ha hb h) slots hs).trans hb.symm)

include profile in
public theorem written_reflection (hΓ : Γ.Pure) {slots : Fin Γ.length → α}
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (code : Shared A e Γ a b)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A ↔ Eqv Γ A e a b := by
  exact ⟨fun native => eqv_of_agrees profile code hΓ (agrees_of_native profile ht hs' native) slots hs,
    fun eq => eq.toLetIter ht hs'⟩

include profile in
private theorem shared_of_agrees (left : Written A e Γ a) :
    ∀ {b : Expr Φ}, Written A e Γ b → Γ.Pure →
      ∀ (slots : Fin Γ.length → α), (∀ i, (Γ.get i).1 = .base (slots i)) →
        Agrees profile Γ A a b → Shared A e Γ a b := by
  induction left with
  | @leaf Γ a value head typed leaf =>
    intro b right hΓ slots hs obs
    cases right with
    | leaf head' typed' leaf' =>
      exact .normalize head head' (.leaf typed typed' leaf leaf')
    | call head' visible' _ typed' leaf' hl _ =>
      exact (leaf_ne_call profile hΓ hs visible' typed leaf typed' leaf' hl
        (agrees_of_eqv profile head head' obs)).elim
  | @call Γ a arg k f head visible bound typed leaf hk _ ih =>
    intro b right hΓ slots hs obs
    cases right with
    | leaf head' typed' leaf' =>
      exact (leaf_ne_call profile hΓ hs visible typed' leaf' typed leaf hk
        (agrees_symm profile (agrees_of_eqv profile head head' obs))).elim
    | @call _ _ arg' l g head' visible' _ typed' leaf' hl children =>
      have calls : Agrees profile Γ A (.let₁ (.op f arg) k) (.let₁ (.op g arg') l) :=
        agrees_of_eqv profile head head' obs
      obtain ⟨opEq, argEq⟩ := call_eq_of_agrees profile hΓ hs visible visible'
        typed typed' leaf leaf' hk hl calls
      subst g
      have align : Eqv Γ A e (.let₁ (.op f arg') l) (.let₁ (.op f arg) l) :=
        .let1 (.op bound argEq.symm) (.refl hl)
      have aligned : Agrees profile Γ A (.let₁ (.op f arg) k) (.let₁ (.op f arg) l) :=
        agrees_of_eqv profile (.refl head.endpoints_wf.2) align calls
      refine .normalize head (head'.trans align) (.call visible bound typed leaf hk hl ?_)
      intro n sorts shape
      have contexts := field_context hΓ hs sorts
      exact ih shape (children shape) contexts.1 _ contexts.2
        (agrees_child profile visible hΓ hs typed leaf hk hl aligned shape)

include profile in
public theorem independent_written_reflection (hΓ : Γ.Pure) {slots : Fin Γ.length → α}
    (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    (left : Written A e Γ a) (right : Written A e Γ b)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A ↔ Eqv Γ A e a b := by
  refine ⟨fun native => ?_, fun eq => eq.toLetIter ht hs'⟩
  have obs : Agrees profile Γ A a b := agrees_of_native profile ht hs' native
  exact eqv_of_agrees profile (shared_of_agrees profile left right hΓ slots hs obs) hΓ obs slots hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection.Proofs
