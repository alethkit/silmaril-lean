module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain

open Diamond (Val ValueSort dataPorts)
open GVN.Elimination (Rewrite Routing)
open SubZero (model)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

/-- All original typed producer and argument reads agree under the
routing returned by a successful step. -/
theorem step_agrees (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.step_agrees accepted entry

/-- Using the routed result preserves the native return at every input. -/
theorem step_eval_eq (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (rewrittenProgram program rewrite).eval model entry = program.eval model entry :=
  (step_agrees accepted entry _ program.result).symm

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain
