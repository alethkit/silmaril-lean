module

public import Silmaril.SSA.SeaOfNodes.MLIR.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.MLIR.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.MLIR

open RVSDG (Origin extend)
open Diamond (Dataflow)
open Silmaril.MLIR.Arith (Env Width)

/-- The lowered block returns the value of the selected source wire on every
typed input, using the existing Sea of Nodes producer-table evaluator. -/
theorem lower_denote {Γ : List Width} {sigs : List (List (Diamond.Ty Width))} {w : Width}
    (flow : Dataflow Op (inputPorts Γ) [] sigs)
    (result : Origin (inputPorts Γ) (extend [] sigs) (.value (.data w))) (env : Env Γ) :
    (lower flow result).denote env =
      Diamond.read model result (sourceInputs env) (flow.eval model (sourceInputs env) PUnit.unit) :=
  Proofs.lower_denote flow result env

end Silmaril.SSA.SeaOfNodes.MLIR
