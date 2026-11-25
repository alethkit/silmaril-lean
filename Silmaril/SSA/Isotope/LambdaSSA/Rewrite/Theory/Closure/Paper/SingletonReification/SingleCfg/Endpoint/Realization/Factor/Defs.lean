module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Defs

/-! # Structural factors of a carried CFG step -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

/-- Rebuild the original state pair alongside a retained copy of its capture. -/
def duplicateCapture : Region Φ :=
  .let₂ (.var 0) (.br 0 (.pair (.var 1) (.pair (.var 1) (.var 0))))

/-- Decode a packed exit and keep the capture in its new exact-sum payload. -/
def retagPacked (S D : τ) : Region Φ :=
  .let₂ (.var 0) ((unpackExits [S, D]).lsubst tagCarriedExit)

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
