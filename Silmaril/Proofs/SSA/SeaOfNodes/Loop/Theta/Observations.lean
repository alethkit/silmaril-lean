module

public import Silmaril.Proofs.SSA.SeaOfNodes.Loop.Theta.Correctness
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.ThetaProofs

open RVSDG (Tuple)
open RVSDG.NestedTheta (MonadicModel)

universe u v w

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out) (m : Model.{u,v,w} Op)
variable (input : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out)

theorem lower_observe :
    g.Returns m input result ↔
      RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (thetaRuntime m)) g.lowerTheta input =
        Part.some (.cons result .nil) :=
  (lower_returns g m input result).trans
    (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns
      (thetaRuntime m) g.lowerTheta input (.cons result .nil)).symm

theorem lower_finishes :
    g.Returns m input result ↔
      RVSDG.NestedTheta.Petri.Finishes (thetaRuntime m) g.lowerTheta input (.cons result .nil) :=
  (lower_returns g m input result).trans (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).symm

end Silmaril.SSA.SeaOfNodes.Loop.ThetaProofs
