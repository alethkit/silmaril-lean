module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Defs

/-! # A syntactic exact-sum step for a captured one-block CFG -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open Silmaril.DeBruijn (lift)

universe u v

variable {Φ : Type v}

/-- Retain the capture in both the repeat and result payloads.
The old state is at slot one and the capture at slot two. -/
def tagCarriedExit : Nat → Region Φ
  | 0 => .br 0 (.inr (.pair (.var 2) (.var 0)))
  | _ + 1 => .br 0 (.inl (.pair (.var 2) (.var 0)))

/-- Unpack the carried state, run the actual decoded block, and retag its two exits. -/
def realizeStep (p : Region Φ) : Region Φ :=
  .let₂ (.var 0) ((p.renameVars (lift (lift Nat.succ))).lsubst tagCarriedExit)

/-- Realize the step of the original packed block, including its exit decoder. -/
def realizePackedStep {τ : Type u} [TypeFormers τ] (S D : τ) (b : Region Φ) : Region Φ :=
  realizeStep (decodeExits (Paper.PackedBody.applyPacked b) [S, D])

/-- Project a loop result to the original outward payload. -/
def dropCapture : Region Φ := .let₂ (.var 0) (.br 0 (.var 0))

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
