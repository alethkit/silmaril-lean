module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs

/-! # CFG feedback for typed continuation families -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} {Φ : Type v}

/-- Close the first `L.length` exits into local CFG blocks and enter the
selected block with the input payload. Remaining exits stay outward. -/
@[expose] def feedbackRegion (L : LCtx τ) (σ : Nat → Region Φ) (i : Nat) : Region Φ :=
  cfgEntryContinuations (fun j : Fin L.length => σ j) i

end Silmaril.Isotope.LambdaSSA.Region
