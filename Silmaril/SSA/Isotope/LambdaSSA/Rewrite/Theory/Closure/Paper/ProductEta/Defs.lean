module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs

/-! # The substitution for unpacking a product variable -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

/-- After unpacking slot `i`, reconstruct it from the new component slots.
The other variables keep their values underneath the two binders. -/
def splitProduct {Φ : Type v} (i j : Nat) : Tm Φ :=
  if j = i then .pair (.var 1) (.var 0) else .var (j + 2)

end Silmaril.Isotope.LambdaSSA.Region.Paper
