module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Defs

/-! # Native terms and set interpretations of normal values -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Value

universe u
variable {α Φ : Type u} (S : Signature α Φ) {n : Nat} {sorts : Fin n → α}

/-- Interpret atomic trees, tuples, unit and injections in the set model. -/
def denote : {A : Ty α} → Value S sorts A → Ty.denote (Tree S sorts) A
  | _, .tree t => t
  | _, .unit => PUnit.unit
  | _, .pair p q => (denote p, denote q)
  | _, .inl p => .inl (denote p)
  | _, .inr q => .inr (denote q)

/-- The native constructor term of a normal value. -/
def native : {A : Ty α} → Value S sorts A → Tm Empty Φ n
  | _, .tree t => t.native
  | _, .unit => .unit
  | _, .pair p q => .pair (native p) (native q)
  | _, .inl p => .inl (native p)
  | _, .inr q => .inr (native q)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Value
