module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection

/-! # Original-bound native reflection for recursive written reply trees -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection

universe u r

/-- The constructor rendering of any reply shape is a written constructor
expression in any placement of its atom fields. -/
theorem shape_constructor {α Φ : Type u} {n m : Nat} {sorts : Fin n → α} {R : Ty α}
    (shape : ReplyShape sorts R) (place : Fin n → Fin m) :
    ConstructorLeaf (shape.source (Φ := Φ) place) :=
  Proofs.shape_constructor shape place

section Written

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {A : Ty α} {Γ : EffectCtx (Ty α) ε} {e : ε}

theorem Written.of_leaf {a : Expr Φ} (typed : Wf Γ a A ⊥) (leaf : ConstructorLeaf a) :
    Written A e Γ a :=
  .leaf (.refl (typed.weakenEffect bot_le)) typed leaf

theorem Written.of_call {f : Φ} {arg k : Expr Φ}
    (visible : ¬ IsPure (⊥ : ε) f) (bound : instrEff f ≤ e)
    (typed : Wf Γ arg (instrSrc f) ⊥) (leaf : ConstructorLeaf arg)
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e)
    (children : ∀ {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts (instrTrg f)),
      Written A e (ReplyShape.fieldCtx sorts Γ) (shape.specialize Γ k)) :
    Written A e Γ (.let₁ (.op f arg) k) :=
  .call (.refl (.let₁ (.op bound (typed.weakenEffect bot_le)) hk)) visible bound typed leaf hk children

end Written

variable {α Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α]
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {A : Ty α} {Γ : EffectCtx (Ty α) ε} {e : ε} {a b : Expr Φ}

/-- Native abort equivalence reflects to the same fixed-bound source
equation for a pair of written endpoints in the shared-request grammar. -/
theorem written_reflection (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
    {slots : Fin Γ.length → α} (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    (code : Shared A e Γ a b) {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A ↔ Eqv Γ A e a b :=
  Proofs.written_reflection profile hΓ hs code ht hs'

/-- Native equality of two visible calls recovers the opcode and a source
equation between their constructor arguments at the supplied bound. -/
theorem call_request_inversion (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
    {slots : Fin Γ.length → α} (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    {f g : Φ} (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g) {arg arg' k l : Expr Φ}
    (ha : Wf Γ arg (instrSrc f) ⊥) (hb : Wf Γ arg' (instrSrc g) ⊥)
    (la : ConstructorLeaf arg) (lb : ConstructorLeaf arg')
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) (hl : Wf ((instrTrg g, ⊥) :: Γ) l A e)
    {t s : Tm Empty Φ Γ.length}
    (ht : (Expr.let₁ (.op f arg) k).toLetIter Γ.length = some t)
    (hs' : (Expr.let₁ (.op g arg') l).toLetIter Γ.length = some s)
    (native : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A) :
    f = g ∧ Eqv Γ (instrSrc f) e arg arg' :=
  Proofs.call_request_inversion profile hΓ hs hf hg ha hb la lb hk hl ht hs' native

/-- Independently recognized endpoints reflect native equality at the
original bound. Request and argument agreement are recovered by the proof. -/
theorem independent_written_reflection (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
    {slots : Fin Γ.length → α} (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    (left : Written A e Γ a) (right : Written A e Γ b)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A ↔ Eqv Γ A e a b :=
  Proofs.independent_written_reflection profile hΓ hs left right ht hs'

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection
