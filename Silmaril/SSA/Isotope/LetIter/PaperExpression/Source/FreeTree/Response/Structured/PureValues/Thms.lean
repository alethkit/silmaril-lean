module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

/-! # Faithful pure constructor values and original-bound empty-reply reflection -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

universe u r

section Values

variable {α Φ : Type u} [HasTy Φ (Ty α)]
  {ε : Type r} [HasEff Φ ε] [Bot ε] {n : Nat} {slots : Fin n → α} {A : Ty α}

/-- Decoding recovers all constructor tags, variables and primitive
applications from the semantic value. -/
theorem decode_encode (v : Value (Φ := Φ) (ε := ε) slots A) :
    Value.decode A v.encode = v :=
  Proofs.decode_encode v

/-- The free value algebra separates typed constructor representatives. -/
theorem encode_injective : Function.Injective (Value.encode (Φ := Φ) (ε := ε) (slots := slots) (A := A)) :=
  Proofs.encode_injective

/-- The variable valuation leaves the free value unchanged. -/
theorem subst_var (v : Value (Φ := Φ) (ε := ε) slots A) :
    v.subst Value.var = v :=
  Proofs.subst_var v

/-- The written value lowers to its canonical native rendering. -/
theorem lowers (v : Value (Φ := Φ) (ε := ε) slots A) :
    v.source.toLetIter n = some v.native :=
  Proofs.lowers v

section Typing

variable [Preorder ε] {Γ : EffectCtx (Ty α) ε}
  {sorts : Fin Γ.length → α}

/-- The source rendering is bottom-typed in its pure atomic context. -/
theorem wf (v : Value (Φ := Φ) (ε := ε) sorts A) (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) :
    Wf Γ v.source A (⊥ : ε) :=
  Proofs.wf v hΓ hs

end Typing

section Model

variable (profile : Profile (α := α) Φ ε)

local notation "V" => Atom (Φ := Φ) (ε := ε) slots
local notation "D" => Ty.denote (Lifted V)
local notation "M" => instructions V (pureMaps slots profile)
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

/-- The native rendering returns the substituted value at any sorted valuation
of free atoms. The model can have further generators, including a fresh reply. -/
theorem denote_value_at {m : Nat} (modelSlots : Fin m → α)
    {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i))
    (v : Value (Φ := Φ) (ε := ε) slots A)
    (vars : (i : Fin n) → Atom (Φ := Φ) (ε := ε) modelSlots (slots i)) :
    let W := Atom (Φ := Φ) (ε := ε) modelSlots
    (v.derivation hs).denote (Ty.denote (Lifted W)) (instructions W (pureMaps modelSlots profile))
      (fun z => z.elim) (valuationEnv slots modelSlots hs vars) =
      ITree.ret ((toSmall W A).symm (v.subst vars).encode) :=
  Proofs.denote_value_at profile modelSlots hs v vars

/-- At the canonical valuation the native rendering immediately returns
the encoded constructor value in the structured-request model. -/
theorem denote_value {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i))
    (v : Value (Φ := Φ) (ε := ε) slots A) :
    (v.derivation hs).denote D M (fun z => z.elim) (variableEnv slots hs) =
      ITree.ret ((toSmall V A).symm v.encode) :=
  Proofs.denote_value profile hs v

include profile in
/-- An arbitrary native abort equivalence between two rendered values
identifies their constructor representatives. -/
theorem value_eq_of_abortEquiv [DecidableEq α] {β : BoundCtx (Ty α) n}
    (hs : ∀ i, β.get i = .base (slots i))
    {p q : Value (Φ := Φ) (ε := ε) slots A}
    (h : AbortEquiv (⊥ : ε) Γ₀ β p.native q.native A) : p = q :=
  Proofs.value_eq_of_abortEquiv profile hs h

include profile in
/-- Native equality recovers the original visible primitive and its full
constructor argument, for arbitrary typed native continuations. -/
theorem request_eq_of_abortEquiv [DecidableEq α] {β : BoundCtx (Ty α) n}
    (hs : ∀ i, β.get i = .base (slots i))
    {f g : Φ} (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g)
    {p : Value (Φ := Φ) (ε := ε) slots (instrSrc f)}
    {q : Value (Φ := Φ) (ε := ε) slots (instrSrc g)}
    {t s : Tm Empty Φ (n + 1)} (dt : Derivation Φ Γ₀ (β.snoc (instrTrg f)) t A)
    (ds : Derivation Φ Γ₀ (β.snoc (instrTrg g)) s A)
    (h : AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (.op f p.native) t) (.let₁ (.op g q.native) s) A) :
    (⟨f, p⟩ : (i : Φ) × Value (Φ := Φ) (ε := ε) slots (instrSrc i)) = ⟨g, q⟩ :=
  Proofs.request_eq_of_abortEquiv profile hs hf hg dt ds h

end Model

end Values

section Normalization

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε]
  [PartialOrder ε] [OrderBot ε] (profile : Profile (α := α) Φ ε)
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α} {A : Ty α}

local notation "Val" => Value (Φ := Φ) (ε := ε) slots

include profile in
/-- Normalize bottom-typed constructor expressions at the supplied bound.
Pure unit-result primitives use the existing source terminality rule. -/
theorem normalize_leaf {a : Expr Φ} (ha : Wf Γ a A (⊥ : ε)) (hLeaf : ConstructorLeaf a)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε) :
    ∃ v : Val A, Eqv Γ A e a v.source :=
  Proofs.normalize_leaf profile ha hLeaf hΓ hs e

end Normalization

section Reflection

variable {α Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α]
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  (profile : Profile (α := α) Φ ε) {Γ : EffectCtx (Ty α) ε}
  {slots : Fin Γ.length → α} {A : Ty α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

include profile in
/-- Original-bound source equality of constructor representatives is exactly
native abort equivalence of their renderings. -/
theorem leaf_reflection (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Value (Φ := Φ) (ε := ε) slots A) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx p.native q.native A ↔ Eqv Γ A e p.source q.source :=
  Proofs.leaf_reflection profile hΓ hs e p q

include profile in
/-- Reflect native equality of two visible empty-reply calls at the original
bound. Their primitive labels and typed constructor arguments are recovered
before using source initiality for the continuations. -/
theorem empty_reply_reflection
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
      Eqv Γ A e (.let₁ (.op f p.source) k) (.let₁ (.op g q.source) l) :=
  Proofs.empty_reply_reflection profile hΓ hs hf hg emptyReply atBound p q hk hl ht hs'

/-- Equality at the canonical valuation reflects the original-bound source
equations of raw bottom-typed constructor expressions. -/
theorem constructor_denote_iff
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    {a b : Expr Φ} (ha : Wf Γ a A (⊥ : ε)) (hb : Wf Γ b A (⊥ : ε))
    (hLeafA : ConstructorLeaf a) (hLeafB : ConstructorLeaf b)
    {t s : Tm Empty Φ Γ.length} (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s)
    (da : Derivation Φ Γ₀ Γ.toBoundCtx t A) (db : Derivation Φ Γ₀ Γ.toBoundCtx s A) :
    let hslots := fun i => (EffectCtx.get_toBoundCtx Γ i).trans (hs i)
    let ρ := variableEnv (Φ := Φ) (ε := ε) slots hslots
    da.denote (Ty.denote (Lifted (Atom (Φ := Φ) (ε := ε) slots))) (instructions (Atom (Φ := Φ) (ε := ε) slots) (pureMaps slots profile)) (fun x => x.elim) ρ =
      db.denote (Ty.denote (Lifted (Atom (Φ := Φ) (ε := ε) slots))) (instructions (Atom (Φ := Φ) (ε := ε) slots) (pureMaps slots profile))
        (fun x => x.elim) ρ ↔ Eqv Γ A e a b :=
  Proofs.constructor_denote_iff profile hΓ hs e ha hb hLeafA hLeafB ht hs' da db

include profile in
/-- Reflect native equality between bottom-typed written constructor leaves
without supplied constructor normal forms. -/
theorem constructor_reflection
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    {a b : Expr Φ} (ha : Wf Γ a A (⊥ : ε)) (hb : Wf Γ b A (⊥ : ε))
    (hLeafA : ConstructorLeaf a) (hLeafB : ConstructorLeaf b)
    {t s : Tm Empty Φ Γ.length} (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A ↔ Eqv Γ A e a b :=
  Proofs.constructor_reflection profile hΓ hs e ha hb hLeafA hLeafB ht hs'

include profile in
/-- Reflect empty-reply calls on bottom-typed written constructor arguments.
The continuations may be any written terms typed at the original bound. -/
theorem empty_reply_constructor_reflection
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
      Eqv Γ A e (.let₁ (.op f a) k) (.let₁ (.op g b) l) :=
  Proofs.empty_reply_constructor_reflection profile hΓ hs hf hg emptyReply ef eg ha hb hLeafA hLeafB hk hl hu hv ht hs'

end Reflection

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues
