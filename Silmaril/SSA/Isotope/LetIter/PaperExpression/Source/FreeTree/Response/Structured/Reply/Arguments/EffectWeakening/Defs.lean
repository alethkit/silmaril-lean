module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Defs

/-! # Instruction bounds for finite written expressions -/

@[expose] public section

open Silmaril.Isotope

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments

universe u r

/-- Join the effects of the written instructions, including those in both
case arms. Variable-slot effects are independent of this syntactic bound. -/
def instructionBound {Φ : Type u} {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] :
    Expr Φ → ε
  | .var _ | .unit => ⊥
  | .op f a => instrEff f ⊔ instructionBound a
  | .pair a b | .let₁ a b | .let₂ a b => instructionBound a ⊔ instructionBound b
  | .case a l r => instructionBound a ⊔ (instructionBound l ⊔ instructionBound r)
  | .inl a | .inr a | .abort a => instructionBound a

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments
