module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs

/-! # Input types for recursive source context splitting -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection

universe u

variable {α : Type u}

/-- Types generated from atoms by binary products and binary sums. -/
def InputType : Ty α → Prop
  | .base _ => True
  | .product A B | .coprod A B => InputType A ∧ InputType B
  | .unit | .empty => False

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection
