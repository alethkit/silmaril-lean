module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallITree

/-! # Visible behavior of the computed call -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.Example.ITree

/-- The explicit sequencing makes one producer request and passes its reply to a single consumer request. -/
theorem sequenced_visible (x : PayloadValue) :
    (interpretation.map sequencedArrow).of x = expected x :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallITree.sequenced_visible x

/-- The nested source call has the same ordered requests for every input and reply. -/
theorem nested_visible (x : PayloadValue) :
    (interpretation.map nestedArrow).of x = expected x :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallITree.nested_visible x

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.Example.ITree
