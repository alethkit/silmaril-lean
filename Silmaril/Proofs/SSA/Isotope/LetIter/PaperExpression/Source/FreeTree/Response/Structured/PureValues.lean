module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Proofs

universe u r

section Values

variable {α Φ : Type u} [HasTy Φ (Ty α)]
  {ε : Type r} [HasEff Φ ε] [Bot ε] {n : Nat} {slots : Fin n → α} {A : Ty α}

public theorem decode_encode (v : Value (Φ := Φ) (ε := ε) slots A) :
    Value.decode A v.encode = v := by
  induction v with
  | var _ => rfl
  | op _ _ _ _ _ => rfl
  | unit => rfl
  | pair _ _ ihL ihR => simp only [Value.encode, Value.decode, ihL, ihR]
  | inl _ ih => simp only [Value.encode, Value.decode, ih]
  | inr _ ih => simp only [Value.encode, Value.decode, ih]

public theorem encode_injective : Function.Injective (Value.encode (Φ := Φ) (ε := ε) (slots := slots) (A := A)) :=
  Function.LeftInverse.injective decode_encode

public theorem lowers (v : Value (Φ := Φ) (ε := ε) slots A) :
    v.source.toLetIter n = some v.native := by
  induction v with
  | var _ => simp [Value.source, Value.native, Expr.toLetIter]
  | op _ _ _ _ ih => simp [Value.source, Value.native, Expr.toLetIter, ih]
  | unit => rfl
  | pair _ _ ihL ihR => simp [Value.source, Value.native, Expr.toLetIter, ihL, ihR]
  | inl _ ih => simp [Value.source, Value.native, Expr.toLetIter, ih]
  | inr _ ih => simp [Value.source, Value.native, Expr.toLetIter, ih]

section Typing

variable [Preorder ε] {Γ : EffectCtx (Ty α) ε}
  {sorts : Fin Γ.length → α}

public theorem wf (v : Value (Φ := Φ) (ε := ε) sorts A) (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) :
    Wf Γ v.source A (⊥ : ε) := by
  induction v with
  | var i => simpa only [Value.source, hs i] using Wf.var (Φ := Φ) i (hΓ i).le
  | op f hf h _ ih => simpa only [Value.source, h] using Wf.op (f := f) hf.le ih
  | unit => exact .unit _ _
  | pair _ _ ihL ihR => exact .pair ihL ihR
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

end Typing

section Model

set_option backward.isDefEq.respectTransparency false

variable (profile : Profile (α := α) Φ ε)

local notation "V" => Atom (Φ := Φ) (ε := ε) slots
local notation "D" => Ty.denote (Lifted V)
local notation "M" => instructions V (pureMaps slots profile)
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

private theorem pureMap_atom {f : Φ} (hf : IsPure (⊥ : ε) f) {a : α}
    (h : instrTrg f = .base a) (x : Ty.denote V (instrSrc f)) :
    cast (congrArg (Ty.denote V) h) (pureMaps slots profile f hf x) =
      (Value.op f hf (a := a) h (Value.decode (instrSrc f) x)).encode := by
  unfold pureMaps
  split
  · rename_i b hb _
    have hab := Ty.base.inj (h.symm.trans hb)
    subst b
    simp
    rfl
  · rename_i hu _
    cases h.symm.trans hu

private theorem denote_cast {β : BoundCtx (Ty α) n} {t : Tm Empty Φ n} {B C : Ty α}
    (h : B = C) (d : Derivation Φ Γ₀ β t B) (ρ : BoundEnv D β) :
    (cast (congrArg (Derivation Φ Γ₀ β t) h) d).denote D M (fun z => z.elim) ρ =
      cast (congrArg (fun X => ITree.Tree (Event (Φ := Φ) V) (D X)) h)
        (d.denote D M (fun z => z.elim) ρ) := by
  cases h
  rfl

private theorem cast_ret {B C : Ty α} (h : B = C) (x : D B) :
    cast (congrArg (fun X => ITree.Tree (Event (Φ := Φ) V) (D X)) h) (ITree.ret x) =
      ITree.ret (cast (congrArg D h) x) := by
  cases h
  rfl

private theorem cast_lift {B C : Ty α} (h : B = C) (x : Ty.denote V B) :
    cast (congrArg D h) ((toSmall V B).symm x) =
      (toSmall V C).symm (cast (congrArg (Ty.denote V) h) x) := by
  cases h
  rfl

private theorem ret_bind {E : Type u → Type u} {X Y : Type (u + 1)}
    (x : X) (k : X → ITree.Tree E Y) : (ITree.ret x >>= k) = k x :=
  pure_bind x k

public theorem denote_value {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i))
    (v : Value (Φ := Φ) (ε := ε) slots A) :
    (v.derivation hs).denote D M (fun z => z.elim) (variableEnv slots hs) =
      ITree.ret ((toSmall V A).symm v.encode) := by
  classical
  induction v with
  | var i =>
    rw [Value.derivation, denote_cast profile (hs i), Derivation.denote]
    change cast (congrArg (fun X => ITree.Tree (Event (Φ := Φ) V) (D X)) (hs i))
      (ITree.ret (variableEnv slots hs i)) = _
    rw [cast_ret (hs i)]
    change ITree.ret (cast (congrArg D (hs i)) (cast (congrArg D (hs i).symm) ⟨Value.var i⟩)) =
      ITree.ret ⟨Value.var i⟩
    simp
  | op f hf h arg ih =>
    rw [Value.derivation, denote_cast profile h, Derivation.denote, ih]
    change cast (congrArg (fun X => ITree.Tree (Event (Φ := Φ) V) (D X)) h)
      ((pure ((toSmall V (instrSrc f)).symm arg.encode) >>= (M).eval f)) = _
    rw [pure_bind]
    simp only [instructions, hf, dite_true, _root_.Equiv.apply_symm_apply]
    rw [cast_ret h, cast_lift h, pureMap_atom profile hf h, decode_encode]
  | unit => rfl
  | pair _ _ ihL ihR =>
    simp only [Value.derivation, Derivation.denote, ihL, ihR]
    rw [ret_bind, ret_bind]
    rfl
  | inl _ ih =>
    simp only [Value.derivation, Derivation.denote, ih]
    rw [ret_bind]
    rfl
  | inr _ ih =>
    simp only [Value.derivation, Derivation.denote, ih]
    rw [ret_bind]
    rfl

include profile in
public theorem value_eq_of_abortEquiv [DecidableEq α] {β : BoundCtx (Ty α) n}
    (hs : ∀ i, β.get i = .base (slots i))
    {p q : Value (Φ := Φ) (ε := ε) slots A}
    (h : AbortEquiv (⊥ : ε) Γ₀ β p.native q.native A) : p = q := by
  have eq := sound V (pureMaps slots profile) h (p.derivation hs) (q.derivation hs) (variableEnv slots hs)
  rw [denote_value profile hs p, denote_value profile hs q, ITree.ret_inj] at eq
  exact encode_injective ((toSmall V A).symm.injective eq)

include profile in
public theorem request_eq_of_abortEquiv [DecidableEq α] {β : BoundCtx (Ty α) n}
    (hs : ∀ i, β.get i = .base (slots i))
    {f g : Φ} (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g)
    {p : Value (Φ := Φ) (ε := ε) slots (instrSrc f)}
    {q : Value (Φ := Φ) (ε := ε) slots (instrSrc g)}
    {t s : Tm Empty Φ (n + 1)} (dt : Derivation Φ Γ₀ (β.snoc (instrTrg f)) t A)
    (ds : Derivation Φ Γ₀ (β.snoc (instrTrg g)) s A)
    (h : AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (.op f p.native) t) (.let₁ (.op g q.native) s) A) :
    (⟨f, p⟩ : (i : Φ) × Value (Φ := Φ) (ε := ε) slots (instrSrc i)) = ⟨g, q⟩ := by
  have eq := sound V (pureMaps slots profile) h
    (.let₁ (.op (p.derivation hs)) dt) (.let₁ (.op (q.derivation hs)) ds) (variableEnv slots hs)
  rw [denote_letOp_of_not_pure V (pureMaps slots profile) hf,
    denote_letOp_of_not_pure V (pureMaps slots profile) hg,
    denote_value profile hs p, denote_value profile hs q, ret_bind, ret_bind] at eq
  have request := request_eq_of_vis_eq V eq
  simp only [_root_.Equiv.apply_symm_apply] at request
  simpa only [decode_encode] using congrArg
    (fun r : Request (Φ := Φ) V => (⟨r.1, Value.decode _ r.2⟩ :
      (i : Φ) × Value (Φ := Φ) (ε := ε) slots (instrSrc i))) request

end Model
end Values

section Normalization

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε]
  [PartialOrder ε] [OrderBot ε] (profile : Profile (α := α) Φ ε)
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α} {A : Ty α}

local notation "Val" => Value (Φ := Φ) (ε := ε) slots

private theorem source_cast {X Y : Ty α} (h : X = Y) (v : Val X) :
    (cast (congrArg Val h) v).source = v.source := by
  cases h
  rfl

include profile in
public theorem normalize_leaf {a : Expr Φ} (ha : Wf Γ a A (⊥ : ε)) (hLeaf : ConstructorLeaf a)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε) :
    ∃ v : Val A, Eqv Γ A e a v.source := by
  induction hLeaf generalizing A with
  | var _ =>
    cases ha with
    | var i _ =>
      let v : Val (.base (slots i)) := .var i
      refine ⟨cast (congrArg Val (hs i).symm) v, ?_⟩
      rw [source_cast (hs i).symm v]
      exact Eqv.refl (Wf.var (Φ := Φ) (e := e) i ((hΓ i).trans_le bot_le))
  | @op f arg _ ih =>
    cases ha with
    | op hf hArg =>
      have pure : IsPure (⊥ : ε) f := le_antisymm hf bot_le
      cases profile f pure with
      | atom a type =>
        obtain ⟨v, hv⟩ := ih hArg
        let argValue : Val (.base a) := .op f pure type v
        refine ⟨cast (congrArg Val type.symm) argValue, ?_⟩
        rw [source_cast type.symm argValue]
        exact Eqv.op (f := f) (hf.trans bot_le) hv
      | unit type =>
        let value : Val .unit := .unit
        refine ⟨cast (congrArg Val type.symm) value, ?_⟩
        have typed : Wf Γ (.op f arg) (instrTrg f) (⊥ : ε) := .op hf hArg
        have typedUnit : Wf Γ (.op f arg) (Ty.unit : Ty α) (⊥ : ε) := type ▸ typed
        have eq := Eqv.step (Step.terminal (e := e) typedUnit (.unit Γ ⊥))
        rw [source_cast type.symm value]
        exact cast (congrArg (fun T => Eqv Γ T e (.op f arg) .unit) type.symm) eq
  | unit =>
    cases ha
    exact ⟨.unit, .refl (.unit _ _)⟩
  | pair _ _ ihL ihR =>
    cases ha with
    | pair hleft hright =>
      obtain ⟨left, hL⟩ := ihL hleft
      obtain ⟨right, hR⟩ := ihR hright
      exact ⟨.pair left right, .pair hL hR⟩
  | inl _ ih =>
    cases ha with
    | inl hin =>
      obtain ⟨value, he⟩ := ih hin
      exact ⟨.inl value, .inl he⟩
  | inr _ ih =>
    cases ha with
    | inr hin =>
      obtain ⟨value, he⟩ := ih hin
      exact ⟨.inr value, .inr he⟩

end Normalization

section Reflection

variable {α Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α]
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  (profile : Profile (α := α) Φ ε) {Γ : EffectCtx (Ty α) ε}
  {slots : Fin Γ.length → α} {A : Ty α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

include profile in
public theorem leaf_reflection (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Value (Φ := Φ) (ε := ε) slots A) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx p.native q.native A ↔ Eqv Γ A e p.source q.source := by
  constructor
  · intro h
    have hEq := value_eq_of_abortEquiv profile
      (fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i)) h
    subst q
    exact .refl ((wf p hΓ hs).weakenEffect bot_le)
  · intro h
    exact h.toLetIter (lowers p) (lowers q)

include profile in
public theorem empty_reply_reflection
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    {f g : Φ} (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g)
    (emptyReply : instrTrg f = (Ty.empty : Ty α)) {e : ε} (atBound : instrEff f ≤ e)
    (p : Value (Φ := Φ) (ε := ε) slots (instrSrc f))
    (q : Value (Φ := Φ) (ε := ε) slots (instrSrc g))
    {k l : Expr Φ} (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e)
    (hl : Wf ((instrTrg g, ⊥) :: Γ) l A e)
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : k.toLetIter (Γ.length + 1) = some t) (hs' : l.toLetIter (Γ.length + 1) = some s) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (.let₁ (.op f p.native) t) (.let₁ (.op g q.native) s) A ↔
      Eqv Γ A e (.let₁ (.op f p.source) k) (.let₁ (.op g q.source) l) := by
  constructor
  · intro hn
    obtain ⟨t', ht', wt⟩ := hk.toLetIter
    obtain ⟨s', hsEnd, ws⟩ := hl.toLetIter
    have htEq := Option.some.inj (ht'.symm.trans ht)
    have hsEq := Option.some.inj (hsEnd.symm.trans hs')
    subst t'
    subst s'
    obtain ⟨dt⟩ := Derivation.ofHasType wt.1
    obtain ⟨ds⟩ := Derivation.ofHasType ws.1
    have req := request_eq_of_abortEquiv profile
      (fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i)) hf hg dt ds hn
    have sym := congrArg Sigma.fst req
    change f = g at sym
    subst g
    have arg := eq_of_heq (Sigma.mk.inj req).2
    subst q
    have cont := eqv_of_empty_slot (Γ := (instrTrg f, ⊥) :: Γ) 0 emptyReply rfl hk hl
    exact .let1 (.refl (.op atBound ((wf p hΓ hs).weakenEffect bot_le))) cont
  · intro h
    apply h.toLetIter
    · simp only [Expr.toLetIter, lowers p, ht, Option.map_some, Option.bind_some]
    · simp only [Expr.toLetIter, lowers q, hs', Option.map_some, Option.bind_some]

public theorem constructor_denote_iff
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    {a b : Expr Φ} (ha : Wf Γ a A (⊥ : ε)) (hb : Wf Γ b A (⊥ : ε))
    (hLeafA : ConstructorLeaf a) (hLeafB : ConstructorLeaf b)
    {t s : Tm Empty Φ Γ.length} (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s)
    (da : Derivation Φ Γ₀ Γ.toBoundCtx t A) (db : Derivation Φ Γ₀ Γ.toBoundCtx s A) :
    let hslots := fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i)
    let ρ := variableEnv (Φ := Φ) (ε := ε) slots hslots
    da.denote (Ty.denote (Lifted (Atom (Φ := Φ) (ε := ε) slots))) (instructions (Atom (Φ := Φ) (ε := ε) slots) (pureMaps slots profile)) (fun x => x.elim) ρ =
      db.denote (Ty.denote (Lifted (Atom (Φ := Φ) (ε := ε) slots))) (instructions (Atom (Φ := Φ) (ε := ε) slots) (pureMaps slots profile))
        (fun x => x.elim) ρ ↔ Eqv Γ A e a b := by
  let hslots := fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i)
  let ρ := variableEnv (Φ := Φ) (ε := ε) slots hslots
  let V := Atom (Φ := Φ) (ε := ε) slots
  let P := pureMaps slots profile
  refine ⟨fun h => ?_, fun eq => sound V P (eq.toLetIter ht hs') da db ρ⟩
  obtain ⟨p, hp⟩ := normalize_leaf profile ha hLeafA hΓ hs e
  obtain ⟨q, hq⟩ := normalize_leaf profile hb hLeafB hΓ hs e
  have hP := sound V P (hp.toLetIter ht (lowers p)) da (p.derivation hslots) ρ
  have hQ := sound V P (hq.toLetIter hs' (lowers q)) db (q.derivation hslots) ρ
  have hsVal := (hP.symm.trans h).trans hQ
  rw [denote_value profile hslots p, denote_value profile hslots q, ITree.ret_inj] at hsVal
  have eq := encode_injective ((toSmall V A).symm.injective hsVal)
  exact hp.trans (eq ▸ hq.symm)

include profile in
public theorem constructor_reflection
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    {a b : Expr Φ} (ha : Wf Γ a A (⊥ : ε)) (hb : Wf Γ b A (⊥ : ε))
    (hLeafA : ConstructorLeaf a) (hLeafB : ConstructorLeaf b)
    {t s : Tm Empty Φ Γ.length} (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A ↔ Eqv Γ A e a b := by
  refine ⟨fun h => ?_, fun eq => eq.toLetIter ht hs'⟩
  obtain ⟨da⟩ := Derivation.ofHasType h.hasType.1
  obtain ⟨db⟩ := Derivation.ofHasType h.hasType.2
  let ρ := variableEnv (Φ := Φ) (ε := ε) slots (fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i))
  exact (constructor_denote_iff profile hΓ hs e ha hb hLeafA hLeafB ht hs' da db).mp
    (sound (Atom (Φ := Φ) (ε := ε) slots) (pureMaps slots profile) h da db ρ)

omit [HasTy Φ (Ty α)] [DecidableEq α] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] in
private theorem lower_let_op {a k : Expr Φ} {f : Φ}
    {arg : Tm Empty Φ Γ.length} {t : Tm Empty Φ (Γ.length + 1)}
    (ha : a.toLetIter Γ.length = some arg) (hk : k.toLetIter (Γ.length + 1) = some t) :
    (Expr.let₁ (.op f a) k).toLetIter Γ.length = some (.let₁ (.op f arg) t) := by
  simp only [Expr.toLetIter, ha, hk, Option.map_some, Option.bind_some]

include profile in
public theorem empty_reply_constructor_reflection
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    {f g : Φ} (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g)
    (emptyReply : instrTrg f = (Ty.empty : Ty α)) {e : ε}
    (ef : instrEff f ≤ e) (eg : instrEff g ≤ e)
    {a b k l : Expr Φ} (ha : Wf Γ a (instrSrc f) (⊥ : ε)) (hb : Wf Γ b (instrSrc g) (⊥ : ε))
    (hLeafA : ConstructorLeaf a) (hLeafB : ConstructorLeaf b)
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) (hl : Wf ((instrTrg g, ⊥) :: Γ) l A e)
    {u v : Tm Empty Φ Γ.length} (hu : a.toLetIter Γ.length = some u) (hv : b.toLetIter Γ.length = some v)
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : k.toLetIter (Γ.length + 1) = some t) (hs' : l.toLetIter (Γ.length + 1) = some s) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (.let₁ (.op f u) t) (.let₁ (.op g v) s) A ↔
      Eqv Γ A e (.let₁ (.op f a) k) (.let₁ (.op g b) l) := by
  refine ⟨fun h => ?_, fun eq => eq.toLetIter (lower_let_op hu ht) (lower_let_op hv hs')⟩
  obtain ⟨p, hp⟩ := normalize_leaf profile ha hLeafA hΓ hs e
  obtain ⟨q, hq⟩ := normalize_leaf profile hb hLeafB hΓ hs e
  have left := Eqv.let1 (Eqv.op ef hp) (.refl hk)
  have right := Eqv.let1 (Eqv.op eg hq) (.refl hl)
  have nL := left.toLetIter (lower_let_op hu ht) (lower_let_op (lowers p) ht)
  have nR := right.toLetIter (lower_let_op hv hs') (lower_let_op (lowers q) hs')
  have middle := (empty_reply_reflection profile hΓ hs hf hg emptyReply ef p q hk hl ht hs').mp
    (.trans (.trans nL.symm h) nR)
  exact left.trans (middle.trans right.symm)

end Reflection


end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Proofs
