module

public import Silmaril.SSA.SeaOfNodes.Loop.Theta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.Theta.Observations

/-! # Finite-return observations of the generated θ graph -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Tuple)
open RVSDG.NestedTheta (MonadicModel)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out) (m : Model.{u,v,w} Op)
variable (input : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out)

/-- The numbered target returns the singleton value tuple at some finite
θ bound exactly when the source returns the value. -/
theorem Graph.lowerTheta_returns_iff :
    g.Returns m input result ↔ g.lowerTheta.Returns (thetaRuntime m) input (.cons result .nil) :=
  ThetaProofs.lower_returns g m input result

/-- The target's existing partial denotation observes exactly the finite
returns of the source loop, with total interpretations of the generated leaves. -/
theorem Graph.lowerTheta_observe_eq_some :
    g.Returns m input result ↔
      RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (thetaRuntime m)) g.lowerTheta input =
        Part.some (.cons result .nil) :=
  ThetaProofs.lower_observe g m input result

/-- A finite completed firing sequence has exactly the source return
observation. This is an existential completion statement. -/
theorem Graph.lowerTheta_finishes_iff :
    g.Returns m input result ↔ RVSDG.NestedTheta.Petri.Finishes (thetaRuntime m) g.lowerTheta input (.cons result .nil) :=
  ThetaProofs.lower_finishes g m input result

end Silmaril.SSA.SeaOfNodes.Loop
