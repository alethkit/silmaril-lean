module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms

/-! # The two-exit numbered graph with genuinely partial instructions -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial

open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (point)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B C D : τ}

/-- The explicit actions use the same partial instructions as the ordered
interpretation. The input and successful output both have their own token. -/
abbrev wireModel :=
  NestedTheta.ExplicitRuntime.Partial.wireModel
    (orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))

/-- Finite execution of the admitted numbered graph at the original typed exit. -/
def returns (s : Blocks Φ A B C D) (a : TyDen A) (initial : σ)
    (label : LabelDen [C, D]) (final : σ) : Prop :=
  NestedTheta.Partial.returns (wireModel (ε := ε)) (graph s) (point (enter a) initial)
    (point (finish (exitPayload label)) final)

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial
