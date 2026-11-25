module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Placed

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}
variable {p q : FixedDrawing S a.profile b.profile}

/-- Extend an active endpoint comparison across the two strips. The idle
strip uses the comparison's height reparametrization. -/
def comparePlacement (side : ActiveStrip) (idle : FixedCap S)
    (h : p.drawing.CapComparison q.drawing) :
    (side.placeDrawing p idle).drawing.CapComparison (side.placeDrawing q idle).drawing :=
  Proofs.HorizontalComparison.placedComparison side idle h

end Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip
