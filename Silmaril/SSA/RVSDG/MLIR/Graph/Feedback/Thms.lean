module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Thms
import Silmaril.Proofs.SSA.RVSDG.MLIR.Graph.Feedback.Correctness

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback

open NestedTheta.Institution
open OrderedRuntime.Structured (Values)

universe u v w
variable {V : Type u} {A : Stateless.Signature.{u,v} V}
variable {args outs : Ports (PortSort V)} {sigs : List (Ports (PortSort V))}

/-- Lowering preserves and reflects finite execution at the entire ordered
result tuple. The source uses the finite derivation of the numbered graph. -/
theorem returns_lower_iff (m : Stateless.Model.{u,v,w} A)
    (g : NestedTheta.Graph A.op args [] sigs outs) (stateFree : Stateless.NoState g.toTerm)
    (input : Tuple (Values m.value) args) (output : Tuple (Values m.value) outs) :
    (lower g stateFree).Returns m input output ↔ NestedTheta.Partial.returns m.partial g input output :=
  Proofs.exec_lowerTerm_iff m g.toTerm input PUnit.unit output

/-- The independent target return relation reads the same observation as the
stateless institution, for every input and every complete ordered output. -/
theorem observe_eq_some_iff (m : Stateless.Model.{u,v,w} A)
    (g : NestedTheta.Graph A.op args [] sigs outs) (stateFree : Stateless.NoState g.toTerm)
    (input : Tuple (Values m.value) args) (output : Tuple (Values m.value) outs) :
    Stateless.observe m g input = Part.some output ↔ (lower g stateFree).Returns m input output :=
  (Stateless.observe_eq_some m g input output).trans (returns_lower_iff m g stateFree input output).symm

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback
