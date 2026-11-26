module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence

/-! # Original-bound reflection for atomic and two-field product replies -/

public section

open Silmaril.Isotope Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression (Wf)
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence

universe u r

section Observation

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {A : Ty α} {n : Nat} {slots : Fin n → α}

local notation "Prog" => Program (Φ := Φ) (ε := ε)
local notation "Val" => Value (Φ := Φ) (ε := ε)
local notation "Atoms" => Atom (Φ := Φ) (ε := ε)

/-- Lower a sequence without changing the scope of any reply binder. -/
theorem lowers (p : Prog A slots) : p.source.toLetIter n = some p.native :=
  Proofs.lowers p

section Denotation

variable (profile : Profile (α := α) Φ ε) {m : Nat} (modelSlots : Fin m → α)
  {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i))
  (vars : (i : Fin n) → Atom (Φ := Φ) (ε := ε) modelSlots (slots i))

/-- A return evaluates its pure constructor value at the given sorted valuation. -/
theorem denote_ret (v : Val slots A) :
    (Program.ret v).denote profile modelSlots hs vars =
      ITree.ret ((toSmall (Atom (Φ := Φ) (ε := ε) modelSlots) A).symm (v.subst vars).encode) :=
  Proofs.denote_ret profile modelSlots hs vars v

/-- A visible request has the full structured input as its label. The continuation
evaluates with its atomic reply prepended to the valuation. -/
theorem denote_call {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {a : α} (ty : (instrTrg f : Ty α) = .base a) (arg : Val slots (instrSrc f)) (next : Prog A (Fin.cases a slots)) :
    (Program.call f visible ty arg next).denote profile modelSlots hs vars =
      ITree.vis (.call f (arg.subst vars).encode) (fun reply =>
        next.denote profile modelSlots (replySlots hs ty)
          (Fin.cases (motive := fun i => (Atom (Φ := Φ) (ε := ε) modelSlots) (Fin.cases a slots i))
            (cast (congrArg (Ty.denote (Atom (Φ := Φ) (ε := ε) modelSlots)) ty) reply) vars)) :=
  Proofs.denote_call profile modelSlots hs vars visible ty arg next

/-- Compare the continuations at any atomic reply and retained valuation.
Taking the extended scope as the model and its variable generators as the
valuation tests the newest variable as a fresh reply. -/
theorem denote_next_eq {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {a : α} (ty : (instrTrg f : Ty α) = .base a) (arg : Val slots (instrSrc f))
    {p q : Prog A (Fin.cases a slots)}
    (vals : (i : Fin (n + 1)) → Atom (Φ := Φ) (ε := ε) modelSlots (Fin.cases (motive := fun _ => α) a slots i))
    (h :
      let retained : (i : Fin n) → Atom (Φ := Φ) (ε := ε) modelSlots (slots i) := fun i => vals i.succ
      (Program.call f visible ty arg p).denote profile modelSlots hs retained =
        (Program.call f visible ty arg q).denote profile modelSlots hs retained) :
    p.denote profile modelSlots (replySlots hs ty) vals =
      q.denote profile modelSlots (replySlots hs ty) vals :=
  Proofs.denote_next_eq profile modelSlots hs visible ty arg vals h

/-- A product binder consumes one visible request and installs its two
reply fields in their respective continuation slots. -/
theorem denote_callPair {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {a b : α} (ty : (instrTrg f : Ty α) = .product (.base a) (.base b))
    (arg : Val slots (instrSrc f)) (next : Prog A (pairSlots a b slots)) :
    (Program.callPair f visible ty arg next).denote profile modelSlots hs vars =
      ITree.vis (.call f (arg.subst vars).encode) (fun reply =>
        let p := cast (congrArg (Ty.denote (Atoms modelSlots)) ty) reply
        next.denote profile modelSlots (pairReplySlots hs a b) (pairValuation p.1 p.2 vars)) :=
  Proofs.denote_callPair profile modelSlots hs vars visible ty arg next

/-- Test product continuations at any two sorted reply fields, retaining
the old valuation. In the extended free model the two fields can be
tested at distinct fresh generators, even when their sorts coincide. -/
theorem denote_nextPair_eq {f : Φ} (visible : ¬ IsPure (⊥ : ε) f)
    {a b : α} (ty : (instrTrg f : Ty α) = .product (.base a) (.base b))
    (arg : Val slots (instrSrc f)) {p q : Prog A (pairSlots a b slots)}
    (vals : (i : Fin (n + 2)) → Atoms modelSlots (pairSlots a b slots i))
    (h :
      let retained : (i : Fin n) → Atoms modelSlots (slots i) := fun i => vals i.succ.succ
      (Program.callPair f visible ty arg p).denote profile modelSlots hs retained =
        (Program.callPair f visible ty arg q).denote profile modelSlots hs retained) :
    p.denote profile modelSlots (pairReplySlots hs a b) vals =
      q.denote profile modelSlots (pairReplySlots hs a b) vals :=
  Proofs.denote_nextPair_eq profile modelSlots hs visible ty arg vals h

end Denotation

variable (profile : Profile (α := α) Φ ε)

/-- Equality in the free-value models at all sorted valuations separates
these finite sequences. -/
theorem eq_of_denote_eq {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i))
    {p q : Prog A slots}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α) (vars : (i : Fin n) → Atoms modelSlots (slots i)),
      p.denote profile modelSlots hs vars = q.denote profile modelSlots hs vars) : p = q :=
  Proofs.eq_of_denote_eq profile hs h

include profile in
/-- Native equality of two compiled sequences determines the entire sequence. -/
theorem eq_of_abortEquiv [DecidableEq α] {β : BoundCtx (Ty α) n}
    (hs : ∀ i, β.get i = .base (slots i)) {p q : Prog A slots}
    (h : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) β p.native q.native A) : p = q :=
  Proofs.eq_of_abortEquiv profile hs h

end Observation

section Source

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {A : Ty α} {n : Nat} {slots : Fin n → α}

/-- Decomposing the evaluated pair with a unary let followed by
destructuring preserves the original type and effect bound. -/
theorem pairLet_bind {Γ : EffectCtx (Ty α) ε} {a b : Ty α} {e : ε}
    {s k : Expr Φ} (hs : Wf Γ s (.product a b) e)
    (hk : Wf ((b, ⊥) :: (a, ⊥) :: Γ) k A e) :
    Eqv Γ A e (.let₂ s k) (.let₁ s (.let₂ (.var 0) k.wk2)) :=
  Proofs.pairLet_bind hs hk

/-- Substitute the constructor pair of fresh slots for the product variable
of a canonical destructuring continuation. The typed result recovers the
body at the same bound. -/
theorem pairLet_specialize {Γ : EffectCtx (Ty α) ε} {a b : Ty α} {e : ε}
    {k : Expr Φ} (hk : Wf ((b, ⊥) :: (a, ⊥) :: Γ) k A e) :
    Eqv ((b, ⊥) :: (a, ⊥) :: Γ) A e
      (ProductSplit.split 0 (.let₂ (.var 0) k.wk2)) k :=
  Proofs.pairLet_specialize hk

/-- Rendering preserves source typing at the common original effect bound. -/
theorem wf {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {e : ε}
    (p : Program (Φ := Φ) (ε := ε) A slots) (hp : p.Within e) : Wf Γ p.source A e :=
  Proofs.wf hΓ hs p hp

end Source

section Normalize

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [PartialOrder ε] [OrderBot ε]
  (profile : Profile (α := α) Φ ε) {A : Ty α} {e : ε} {Γ : EffectCtx (Ty α) ε} {a : Expr Φ}

include profile in
/-- Normalize each written constructor argument and return at the original
bound, retaining the ordering of the visible requests. -/
theorem normalize (h : Written A e Γ a) :
    ∀ (slots : Fin Γ.length → α), Γ.Pure →
      (∀ i, (Γ.get i).1 = .base (slots i)) →
      ∃ p : Program (Φ := Φ) (ε := ε) A slots, p.Within e ∧ Eqv Γ A e a p.source :=
  Proofs.normalize profile h

end Normalize

section Reflection

variable {α Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α]
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  (profile : Profile (α := α) Φ ε) {A : Ty α} {Γ : EffectCtx (Ty α) ε}
  {slots : Fin Γ.length → α}

include profile in
/-- Native equality of compiled sequences reflects to source Eqv at the
supplied effect bound. -/
theorem endpoint_reflection (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {e : ε}
    (p q : Program (Φ := Φ) (ε := ε) A slots) (hp : p.Within e) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native A ↔
      Eqv Γ A e p.source q.source :=
  Proofs.endpoint_reflection profile hΓ hs p q hp

include profile in
/-- Original-bound reflection for written finite call sequences with atomic
or destructured two-atom product replies and bottom-typed constructor
arguments and returns. -/
theorem written_reflection
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) {e : ε}
    {a b : Expr Φ} (ha : Written A e Γ a) (hb : Written A e Γ b)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A ↔ Eqv Γ A e a b :=
  Proofs.written_reflection profile hΓ hs ha hb ht hs'

end Reflection

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence
