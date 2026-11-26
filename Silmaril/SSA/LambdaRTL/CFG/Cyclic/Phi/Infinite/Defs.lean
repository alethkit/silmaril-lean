module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Defs

/-! # Infinite internal paths of the predecessor-indexed evaluator -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi

universe v w
variable {V K α : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- The original φ entry succeeds, and each pending transfer successfully
executes a block and produces the next transfer. A stuck step has no such successor. -/
def InfiniteRun (model : Model F Part α) (graph : Graph V K F) (input : V → α) : Prop :=
  ∃ path : Nat → Pending V K α,
    path 0 ∈ execute model none graph.entry input ∧
    ∀ i, Sum.inr (path (i + 1)) ∈ step model graph (path i)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
