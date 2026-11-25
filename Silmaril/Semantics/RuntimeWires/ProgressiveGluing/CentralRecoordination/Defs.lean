module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Thms
public import Silmaril.Semantics.Categories.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

namespace ActiveStrip

variable {a a' : FixedCap S} (side : ActiveStrip)

/-- Place the actual interpolating drawing opposite the selected active
strip. The other strip carries straight strands for the fixed profile. -/
def oppositeRecoordination (active : FixedCap S) (h : a.types = a'.types) :
    FixedDrawing S (side.adjoin active a).profile (side.adjoin active a').profile := by
  cases side
  · exact ActiveStrip.right.placeDrawing (a := a) (b := a') (FixedCap.interpolationDrawing h) active
  · exact ActiveStrip.left.placeDrawing (a := a) (b := a') (FixedCap.interpolationDrawing h) active

end ActiveStrip

namespace FixedCap

/-- Object and whiskering data for the repository's premonoidal interface,
using the left sequential tensor of morphisms. -/
@[expose, instance_reducible]
def geometricMonoidalData (S : Signature.{u,v} O) : MonoidalCategoryStruct (FixedCap S) where
  tensorObj := beside
  whiskerLeft a {_ _} f := whiskerLeftHom a f
  whiskerRight f b := whiskerRightHom b f
  tensorUnit := empty S
  associator := objectAssociator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

end FixedCap

end Silmaril.RuntimeWires.ProgressiveGraph
