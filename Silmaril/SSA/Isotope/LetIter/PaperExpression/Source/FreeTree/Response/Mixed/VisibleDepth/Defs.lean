module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Defs

/-! # Syntactic visible-depth bounds for finite mixed programs -/

@[expose] public section

open Silmaril
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

universe u r

variable {α Φ Ψ : Type u} {S : Signature α Φ} {T : SumSignature α Ψ} {c : α}

/-- The maximum request depth of the normalized tree. -/
def Program.visibleDepth : {n : Nat} → {slots : Fin n → α} → Program S T c slots → Nat
  | _, _, .ret _ => 0
  | _, _, .atom _ _ next => next.visibleDepth + 1
  | _, _, .sum _ _ left right => max left.visibleDepth right.visibleDepth + 1

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- A bound on all visible paths, including requests evaluated inside raw
arguments. It is measured after call-by-value normalization. -/
noncomputable def Raw.Program.visibleDepth {n : Nat} {slots : Fin n → α}
    (p : Raw.Program S T c slots) : Nat :=
  (p.compile (ε := ε) S T).visibleDepth

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed
