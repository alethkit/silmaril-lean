module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Premonoidal.Thms

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory
open scoped MonoidalCategory

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

/-- The tensor comparison uses the ordered concatenation of the two cap
words in their actual half-strip placement. -/
def toSlicedTensorIso (X Y : FixedCap S) :
    (toSliced S).obj X ⊗ (toSliced S).obj Y ≅ (toSliced S).obj (X ⊗ Y) :=
  eqToIso (congrArg (Sliced.Presented.mk (S := S)) (beside_labels X Y).symm)

/-- The geometric empty cap reads as the empty sliced word. -/
def toSlicedUnitIso (S : Signature.{u,v} O) :
    𝟙_ (Sliced.Presented S) ≅ (toSliced S).obj (𝟙_ (FixedCap S)) :=
  eqToIso rfl

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap
