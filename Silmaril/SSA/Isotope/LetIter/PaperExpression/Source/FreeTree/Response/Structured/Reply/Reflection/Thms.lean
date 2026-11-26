module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection.Defs
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

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection
