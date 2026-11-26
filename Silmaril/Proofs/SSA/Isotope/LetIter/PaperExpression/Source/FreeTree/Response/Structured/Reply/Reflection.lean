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
  change k.toLetIter (Γ.length + 1) = some k' at hk'
  change l.toLetIter (Γ.length + 1) = some l' at hl'
  have head := h (t := .let₁ (.op f u) k') (s := .let₁ (.op f u) l')
    (by simp only [Expr.toLetIter, hu, hk', Option.bind_some, Option.map_some])
    (by simp only [Expr.toLetIter, hu, hl', Option.bind_some, Option.map_some])
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
    obtain ⟨t, ht, ⟨dt⟩⟩ := lower_typed ha.endpoints_wf.1
    obtain ⟨s, hs', ⟨ds⟩⟩ := lower_typed hb.endpoints_wf.1
    apply ha.trans ((ih hΓ ?_ slots hs).trans hb.symm)
    intro t' s' ht' hsEnd dt' ds' m model ρ
    let V := Atoms model
    let P := pureMaps model profile
    exact (sound V P (ha.toLetIter ht ht') dt dt' ρ).symm.trans
      ((h ht hs' dt ds model ρ).trans (sound V P (hb.toLetIter hs' hsEnd) ds ds' ρ))

include profile in
public theorem written_reflection (hΓ : Γ.Pure) {slots : Fin Γ.length → α}
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (code : Shared A e Γ a b)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A ↔ Eqv Γ A e a b := by
  refine ⟨fun native => ?_, fun eq => eq.toLetIter ht hs'⟩
  apply eqv_of_agrees profile code hΓ ?_ slots hs
  intro t' s' ht' hsEnd dt ds m model ρ
  have eT := Option.some.inj (ht'.symm.trans ht)
  have eS := Option.some.inj (hsEnd.symm.trans hs')
  subst t'
  subst s'
  exact sound (Atoms model) (pureMaps model profile) native dt ds ρ

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection.Proofs
