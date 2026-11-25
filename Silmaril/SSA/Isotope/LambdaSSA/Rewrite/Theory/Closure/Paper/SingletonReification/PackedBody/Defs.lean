module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs

/-! # Supplying the retained input and payload to a singleton body -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody

universe v
open Silmaril.Isotope.LambdaSSA

/-- Supply the retained input and the new payload to a packed singleton body. -/
def applyPacked {Φ : Type v} (p : Region Φ) : Region Φ :=
  p.substVars (Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody
