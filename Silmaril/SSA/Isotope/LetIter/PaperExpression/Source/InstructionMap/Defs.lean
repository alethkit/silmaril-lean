module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Defs

/-! # Relabelling instructions in source expressions -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.PaperExpression.Expr

universe u v

variable {Φ : Type u} {Ψ : Type v}

/-- Change instruction symbols while preserving the binding structure. -/
def mapInstr (φ : Φ → Ψ) : Expr Φ → Expr Ψ
  | .var i => .var i
  | .op f a => .op (φ f) (mapInstr φ a)
  | .let₁ a b => .let₁ (mapInstr φ a) (mapInstr φ b)
  | .pair a b => .pair (mapInstr φ a) (mapInstr φ b)
  | .unit => .unit
  | .let₂ a b => .let₂ (mapInstr φ a) (mapInstr φ b)
  | .inl a => .inl (mapInstr φ a)
  | .inr a => .inr (mapInstr φ a)
  | .case a l r => .case (mapInstr φ a) (mapInstr φ l) (mapInstr φ r)
  | .abort a => .abort (mapInstr φ a)

end Silmaril.Isotope.LetIter.PaperExpression.Expr
