module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip

universe u v
variable {O : Type u} {S : Signature.{u,v} O} (side : ActiveStrip)

/-- Placing beside the empty cap preserves the ordered type word. -/
theorem empty_types (a : FixedCap S) :
    a.types = (side.adjoin a (FixedCap.empty S)).types := by
  unfold FixedCap.types
  rw [side.adjoin_labels]
  cases side <;> simp [FixedCap.empty, CapProfile.empty]

/-- The component changing from the original cap to its half-strip coordinates. -/
def emptyRecoordinate (a : FixedCap S) : a ≅ (side.whisker (FixedCap.empty S)).obj a :=
  FixedCap.recoordinateIso (side.empty_types a)

end Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip
