module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.CollapseObstruction.Uniformity.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CollapseObstruction.Uniformity

/-! # A checked counterexample to local pure uniformity

The pure state change makes the local simulation square commute. The two
feedback arrows are distinct in the current CFG η quotient.

[Companion rule](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/Uniform.lean#L40)
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction.Uniformity

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open scoped Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction

theorem local_square :
    CfgEta.Eqv [stateType] (selfBody.lsubst (liftLSubstVars mapLocal))
      (pureChange.lsubst (liftLSubstVars (fun _ => selfBody))) [stateType, resultType] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence.local_square

theorem local_quotient_square :
    selfBodyArrow ≫ changeLocalArrow = stateChangeArrow ≫ selfBodyArrow :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence.local_quotient_square

theorem changeLocal_left :
    fromNative.map (stateInterface.appendInl returnInterface) ≫ changeLocalArrow =
      stateChangeArrow ≫ fromNative.map (stateInterface.appendInl returnInterface) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence.changeLocal_left

theorem changeLocal_right :
    fromNative.map (stateInterface.appendInr returnInterface) ≫ changeLocalArrow =
      fromNative.map (stateInterface.appendInr returnInterface) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence.changeLocal_right

theorem local_quotient_failure :
    feedback (X := stateInterface) (Y := returnInterface) selfBodyArrow ≠
      stateChangeArrow ≫ feedback (X := stateInterface) (Y := returnInterface) selfBodyArrow :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence.local_quotient_failure

theorem pureReturn_witness (ε : Type) [HasEff Empty ε] (pe : ε) :
    CfgEta.TypeCategory.PureReturn pe pureStateChange :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence.pureReturn_witness ε pe


end Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction.Uniformity
