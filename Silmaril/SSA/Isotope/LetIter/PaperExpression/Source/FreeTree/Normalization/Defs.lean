module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Defs

/-! # Normal values for pure source expressions -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization

universe u r

variable {α Φ : Type u} (S : Signature α Φ)
variable {n : Nat} {sorts : Fin n → α}

/-- Normal values contain free atomic trees, canonical tuples and known injections. -/
inductive Value (sorts : Fin n → α) : Ty α → Type (u + 1)
  | tree {a : α} : Tree S sorts a → Value sorts (.base a)
  | unit : Value sorts .unit
  | pair {A B : Ty α} : Value sorts A → Value sorts B → Value sorts (.product A B)
  | inl {A B : Ty α} : Value sorts A → Value sorts (.coprod A B)
  | inr {A B : Ty α} : Value sorts B → Value sorts (.coprod A B)

def Value.source : {A : Ty α} → Value S sorts A → Expr Φ
  | _, .tree t => t.source
  | _, .unit => .unit
  | _, .pair p q => .pair (Value.source p) (Value.source q)
  | _, .inl p => .inl (Value.source p)
  | _, .inr q => .inr (Value.source q)

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

def Value.Pure : {A : Ty α} → Value S sorts A → Prop
  | _, .tree t => DeclaredPure (ε := ε) S t
  | _, .unit => True
  | _, .pair p q => Value.Pure p ∧ Value.Pure q
  | _, .inl p => Value.Pure p
  | _, .inr q => Value.Pure q

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization
