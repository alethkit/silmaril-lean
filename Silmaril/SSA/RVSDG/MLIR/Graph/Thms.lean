module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Defs
import Silmaril.Proofs.SSA.RVSDG.MLIR.Graph.Correctness

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph

variable {V : Type} {P : Source V}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}

/-- In every total source model, the scoped MLIR block returns the same ordered
tuple as the numbered graph at the corresponding input assignment. -/
theorem denote_lower (m : Model.{0, 0, 0} P.op)
    (g : RVSDG.Graph P.op args [] sigs outs) (input : Tuple m.Val args) :
    ofAssignment outs (fun i => (lower g i).denote (model m) (toAssignment input)) =
      g.run m input :=
  Proofs.denote_lower m g input

end Silmaril.SSA.RVSDG.MLIR.Graph
