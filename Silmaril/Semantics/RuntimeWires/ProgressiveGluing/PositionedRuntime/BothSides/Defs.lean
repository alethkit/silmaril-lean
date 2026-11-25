module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftWord.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap

open Presentation

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G} {R : List G.Obj}

/-- Place a representative in the left strip and the right value contacts
in the opposite strip as straight wires. -/
def padRightDrawing (P : FixedCap (signature G)) (types : P.types = values R)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    FixedDrawing (signature G) (X.padRight P types).cap.profile (Y.padRight P types).cap.profile :=
  ActiveStrip.left.placeDrawing (a := X.cap) (b := Y.cap) p P

end Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap
