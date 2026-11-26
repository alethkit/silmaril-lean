module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Defs

/-! # Keys for the typed nested feedback instructions -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

inductive Key (τ Φ : Type u)
  | enter (a b k d : τ) (op : Φ)
  | inner (b k : τ) (op : Φ)
  | finish (a b k d : τ) (op : Φ)
  deriving DecidableEq

def opcodeKey : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    Op Φ ins outs → Key τ Φ
  | _, _, .ordered _ _ (.pure op) => nomatch op
  | _, _, .ordered _ _ (.effect (.enter (A := a) (B := b) (K := k) (D := d) op)) =>
    .enter a b k d op.op
  | _, _, .ordered _ _ (.effect (.inner (B := b) (K := k) op)) =>
    .inner b k op.op
  | _, _, .ordered _ _ (.effect (.finish (A := a) (B := b) (K := k) (D := d) op)) =>
    .finish a b k d op.op

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse
