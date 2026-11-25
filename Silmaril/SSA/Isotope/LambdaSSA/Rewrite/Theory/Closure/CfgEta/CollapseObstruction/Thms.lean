module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.CollapseObstruction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CollapseObstruction.Witness

/-! # Duplicate feedback collapse is independent of the current CFG η rules -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction

/-- Even without primitive instructions, the current CFG η relation
cannot identify this nested loop with its duplicate-label collapse. -/
theorem collapse_obstruction : ¬ CfgEta.Eqv [stateType] nested flat [resultType] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence.collapse_obstruction

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction
