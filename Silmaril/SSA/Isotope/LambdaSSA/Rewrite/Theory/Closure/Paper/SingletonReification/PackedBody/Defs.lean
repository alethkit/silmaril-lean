module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs

/-! # Supplying the retained input and payload to a singleton body -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody

universe v
open Silmaril.Isotope.LambdaSSA

/-- Substitute the retained input and new payload for the sole packed input. -/
abbrev inputSubst {Φ : Type v} : Nat → Tm Φ :=
  Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ))

/-- Supply the retained input and new payload to a packed singleton region. -/
def applyPacked {Φ : Type v} (p : Region Φ) : Region Φ :=
  p.substVars inputSubst

/-- Supply the same constructor pair to a packed singleton term. -/
def applyPackedTerm {Φ : Type v} (t : Tm Φ) : Tm Φ :=
  t.subst inputSubst

end Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody
