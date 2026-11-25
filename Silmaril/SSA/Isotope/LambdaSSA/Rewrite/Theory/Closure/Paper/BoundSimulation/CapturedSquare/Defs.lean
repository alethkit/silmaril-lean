module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Defs

/-! # Packed representatives for one retained capture -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.CapturedSquare

open Paper.RetainedLet (unpackBody)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

abbrev Packed (X A : τ) := Silmaril.product X A

/-- Pair the retained value with every feedback payload and forward outward exits. -/
def retainCapture : Nat → Region Φ
  | 0 => .br 0 (.pair (.var 1) (.var 0))
  | i + 1 => labelId (i + 1)

/-- Read both inputs from one pair and retain the capture on feedback. -/
def packedStep (p : Region Φ) : Region Φ :=
  unpackBody (p.lsubst (liftLSubstVars retainCapture))

/-- Evaluate the state term in the original context and return the retained capture with it. -/
def capturedReturn (t : Tm Φ) : Region Φ :=
  .let₁ t (.br 0 (.pair (.var 2) (.var 0)))

def packedReturn (t : Tm Φ) : Region Φ :=
  unpackBody (capturedReturn t)

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.CapturedSquare
