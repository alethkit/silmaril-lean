module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Defs

/-! # Fresh slots for constructor specializations of a reply binder -/

@[expose] public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape

universe u v w

variable {α : Type u} {Φ : Type v} {ε : Type w} [Bot ε] {n : Nat}

/-- Prepend one bottom-annotated slot for each atomic field, in the
left-to-right order of the shape. Ambient slots stay in their old order. -/
def fieldCtx (sorts : Fin n → α) (Γ : EffectCtx (Ty α) ε) : EffectCtx (Ty α) ε :=
  List.ofFn (fun i => (.base (sorts i), ⊥)) ++ Γ

@[simp] theorem fieldCtx_length (sorts : Fin n → α) (Γ : EffectCtx (Ty α) ε) :
    (fieldCtx sorts Γ).length = n + Γ.length := by
  simp [fieldCtx]

def fieldIndex (sorts : Fin n → α) (Γ : EffectCtx (Ty α) ε) (i : Fin n) :
    Fin (fieldCtx sorts Γ).length :=
  (i.castAdd Γ.length).cast (fieldCtx_length sorts Γ).symm

def ambientIndex (sorts : Fin n → α) (Γ : EffectCtx (Ty α) ε) (i : Fin Γ.length) :
    Fin (fieldCtx sorts Γ).length :=
  (i.natAdd n).cast (fieldCtx_length sorts Γ).symm

variable {sorts : Fin n → α} {R : Ty α}

/-- Replace the newest reply variable with a rendered constructor, moving
ambient variables past its fresh fields. -/
def sourceSubst (shape : ReplyShape sorts R) (Γ : EffectCtx (Ty α) ε) : Nat → Expr Φ
  | 0 => shape.source (fieldIndex sorts Γ)
  | j + 1 => .var (n + j)

def specialize (shape : ReplyShape sorts R) (Γ : EffectCtx (Ty α) ε) (body : Expr Φ) : Expr Φ :=
  body.subst (shape.sourceSubst Γ)

/-- The corresponding native substitution uses exactly the same slots. -/
def nativeSubst (shape : ReplyShape sorts R) (Γ : EffectCtx (Ty α) ε) :
    Fin (Γ.length + 1) → Tm Empty Φ (fieldCtx sorts Γ).length :=
  Fin.cases (shape.native (fieldIndex sorts Γ)) (fun i => .bv (ambientIndex sorts Γ i))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape
