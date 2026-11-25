module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Defs

/-! # Source normal-form evidence for a sum specialization -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit

universe u r

variable {α Φ : Type u} (S : FreeTree.Signature α Φ)
  {ε : Type r} [HasEff Φ ε] [Preorder ε] [Bot ε]

/-- A branch expression is related to a pure free tree at its original bound. -/
def NormalizesToTree (Γ : EffectCtx (Ty α) ε) (sorts : Fin Γ.length → α)
    (e : ε) (C : α) (a : Expr Φ) : Prop :=
  letI := S.endpoints
  ∃ t : FreeTree.Tree S sorts C, FreeTree.DeclaredPure (ε := ε) S t ∧
    Eqv Γ (.base C) e a t.source

end Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit
