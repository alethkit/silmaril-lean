module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Comparison

public noncomputable section

/-!
# Horizontal associator in either outer active slot

Keep the other two profiles idle. Nesting two placements and placing
beside their grouped idle profile use the same ordered types. The
associator again sends the cuts 0, 1/4, 1/2, 1 to 0, 1/2, 3/4, 1.
The exact wire correspondence indexes the two drawings by their
original active wire IDs and both idle slot lists. The framed comparison
matches the three blocks and follows every through strand of the
outer interpolating drawings while fixing the outer caps.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory
universe u v
variable {O : Type u} {S : Signature.{u,v} O}

namespace ActiveStrip

variable (side : ActiveStrip) (near far : FixedCap S) {a b : FixedCap S}

/-- Match full traces and ordered incidence in the actual collared
composites of the outer-slot naturality square. -/
def compareOuterAssociator (p : FixedDrawing S a.profile b.profile) :
    ((side.outerSourceDrawing near far p).thenDo
      (FixedCap.interpolationDrawing (side.outerAssociator_types near far b))).drawing.CapComparison
      ((FixedCap.interpolationDrawing (side.outerAssociator_types near far a)).thenDo
        (side.outerTargetDrawing near far p)).drawing :=
  Proofs.OuterAssociator.compare side near far p

theorem outerAssociator_naturality (f : a ⟶ b) :
    (side.outerAssociatorSource near far).map f ≫ (side.outerAssociatorComponent near far b).hom =
      (side.outerAssociatorComponent near far a).hom ≫ (side.outerAssociatorTarget near far).map f :=
  Proofs.OuterAssociator.naturality side near far f

/-- Reassociation is natural in the selected outer slot. The nearer
idle profile is the middle slot of the ordered triple. -/
def outerAssociator :
    side.outerAssociatorSource near far ≅ side.outerAssociatorTarget near far :=
  NatIso.ofComponents (side.outerAssociatorComponent near far)
    (fun f => side.outerAssociator_naturality near far f)

theorem outerAssociator_hom_app (a : FixedCap S) :
    (side.outerAssociator near far).hom.app a = (side.outerAssociatorComponent near far a).hom := by rfl

theorem outerAssociator_inv_app (a : FixedCap S) :
    (side.outerAssociator near far).inv.app a = (side.outerAssociatorComponent near far a).inv := by rfl

end ActiveStrip

namespace FixedCap

/-- Naturality in A, with B and C held idle in the ordered triple A, B, C. -/
def leftAssociator (B C : FixedCap S) :
    ActiveStrip.left.nestedWhisker B C ≅ ActiveStrip.left.groupedWhisker B C :=
  ActiveStrip.left.outerAssociator B C

/-- Naturality in C, with A and B held idle in the ordered triple A, B, C. -/
def rightAssociator (A B : FixedCap S) :
    ActiveStrip.right.groupedWhisker B A ≅ ActiveStrip.right.nestedWhisker B A :=
  ActiveStrip.right.outerAssociator B A

end FixedCap

end Silmaril.RuntimeWires.ProgressiveGraph
