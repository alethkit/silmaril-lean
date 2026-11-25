module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.CollapseObstruction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CollapseObstruction.Witness

/-! # Duplicate feedback collapse is independent of the current CFG η rules -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction

/-- Even without primitive instructions, the current CFG η relation
cannot identify this nested loop with its duplicate-label collapse. The
companion includes that collapse as primitive `Uniform.codiagonal`.

[Companion rule](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/Uniform.lean#L49)
-/
theorem collapse_obstruction : ¬ CfgEta.Eqv [stateType] nested flat [resultType] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence.collapse_obstruction

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction
