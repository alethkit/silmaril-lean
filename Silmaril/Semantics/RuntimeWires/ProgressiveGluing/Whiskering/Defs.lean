module

public import Mathlib.CategoryTheory.Functor.Basic
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Composition
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Identity

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c : FixedCap S}
variable (side : ActiveStrip) (idle : FixedCap S)

/-- Placing a straight identity keeps each strand straight. The
comparison reindexes the wires into the concatenated cap order. -/
def compareIdentity (a : FixedCap S) :
    (side.placeDrawing (a := a) (b := a) (FixedDrawing.identity S a.profile a.inside) idle).drawing.CapComparison
      (FixedDrawing.identity S (side.adjoin a idle).profile (side.adjoin a idle).inside).drawing :=
  Proofs.Whiskering.identityComparison side a idle

/-- Compare the two actual collared drawings by the identity homeomorphism
and the wire correspondence induced by their ordered splice slots. -/
def compareComposition (p : FixedDrawing S a.profile b.profile)
    (q : FixedDrawing S b.profile c.profile) :
    (side.placeDrawing (a := a) (b := c) (p.thenDo q) idle).drawing.CapComparison
      ((side.placeDrawing p idle).thenDo (side.placeDrawing q idle)).drawing :=
  Proofs.Whiskering.compositionComparison side idle p q

end Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip
