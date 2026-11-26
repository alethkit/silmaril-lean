module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Arguments
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Case

/-! # Sequencing finite effectful call arguments and sum cases at their original bound -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (Profile)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε]
  {Γ : EffectCtx (Ty α) ε} {A B : Ty α} {e : ε} {a b k : Expr Φ}

section Source

variable [Preorder ε] [OrderBot ε]

/-- Sequence the visible calls of the initializer before those of the body.
At the return leaf, bottom-typed substitution supplies the body's input. -/
theorem Sequenced.bind (ha : Sequenced e Γ A a) (hk : Sequenced e ((A, ⊥) :: Γ) B k) :
    ∃ p, Eqv Γ B e (.let₁ a k) p ∧ Sequenced e Γ B p :=
  Proofs.sequence ha hk

/-- Normalize raw calls, unary lets, and ordered pairs using source equations
at the supplied effect bound. Constructor leaves and arguments stay bottom-typed. -/
theorem Raw.normalize (h : Raw e Γ A a) : ∃ p, Eqv Γ A e a p ∧ Sequenced e Γ A p :=
  Proofs.normalize h

/-- A sequenced form meets the recursive reply-tree recognizer. Reply
specialization substitutes a constructor leaf for the whole structured reply. -/
theorem Sequenced.written (h : Sequenced e Γ A a) : ReplyReflection.Written A e Γ a :=
  Proofs.written h

/-- Every raw expression independently meets the recursive reply-tree
recognizer by normalization at its original bound. -/
theorem Raw.written (h : Raw e Γ A a) : ReplyReflection.Written A e Γ a :=
  Proofs.raw_written h

end Source

/-- Native abort equivalence on lowered raw endpoints coincides with source
equality at their original effect bound. The two raw derivations are independent. -/
theorem raw_reflection [DecidableEq α] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
    {slots : Fin Γ.length → α} (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    (left : Raw e Γ A a) (right : Raw e Γ A b)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A ↔ Eqv Γ A e a b :=
  ReplyReflection.independent_written_reflection profile hΓ hs left.written right.written ht hs'

/-- Evaluate the scrutinee once. The case under the binder reads that
reply, preserving its arms and the original typing bound. -/
theorem case_eqv_bind [Preorder ε] [OrderBot ε] {C : Ty α} {s l r : Expr Φ}
    (hs : Wf Γ s (.coprod A B) e) (hl : Wf ((A, ⊥) :: Γ) l C e)
    (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (.case s l r) (.let₁ s (.case (.var 0) l.wk1 r.wk1)) :=
  Proofs.case_eqv_bind hs hl hr

/-- Normalize branching raw syntax to the recursive reply recognizer.
Sequencing exposes the scrutinee calls in order. After each reply
specialization, a sum-valued constructor leaf selects its typed arm. -/
theorem CaseRaw.written [PartialOrder ε] [OrderBot ε] (profile : Profile (α := α) Φ ε)
    (atomic : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = Ty.base x) (h : CaseRaw e Γ A a) :
    ReplyReflection.Written A e Γ a :=
  Proofs.case_raw_written profile atomic h

/-- Original-bound reflection for cases on a straight-line computed sum,
with recursively branching arms. Each endpoint is recognized independently. -/
theorem case_reflection [DecidableEq α] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
    {slots : Fin Γ.length → α} (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    (left : CaseRaw e Γ A a) (right : CaseRaw e Γ A b)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs' : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A ↔ Eqv Γ A e a b :=
  ReplyReflection.independent_written_reflection profile hΓ hs
    (left.written profile (fun i => ⟨slots i, hs i⟩))
    (right.written profile (fun i => ⟨slots i, hs i⟩)) ht hs'

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments
