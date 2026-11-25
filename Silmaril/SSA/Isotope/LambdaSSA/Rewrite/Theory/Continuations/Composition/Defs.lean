module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # Composition of typed continuation families as linked CFGs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region

universe u v

/-- Run the first continuation, then link its exits to the second
family. The first continuation's incoming argument is not captured by the second. -/
def linkCompLSubst {τ : Type u} {Φ : Type v} (K : LCtx τ)
    (first after : Nat → Region Φ) (i : Nat) : Region Φ :=
  (first i).linkExits K (liftLSubstVars after)

end Silmaril.Isotope.LambdaSSA.Region
