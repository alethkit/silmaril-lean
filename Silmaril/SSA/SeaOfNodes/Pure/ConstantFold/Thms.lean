module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold

open Diamond (Val ValueSort dataPorts)
open SubZero (model)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Folding retains the exact result-port signatures. -/
theorem fold_sigs (program : Program SubZero.Opcode inputs out) :
    (fold program).sigs = program.sigs := rfl

/-- Every final producer slot contains the same typed value. -/
theorem fold_locals_eq (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (fold program).dataflow.eval model entry PUnit.unit = program.dataflow.eval model entry PUnit.unit :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.program_locals_eq program entry

/-- The native return is unchanged at every typed input. -/
theorem fold_eval_eq (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (fold program).eval model entry = program.eval model entry :=
  congrArg (Diamond.read model program.result entry) (fold_locals_eq program entry)

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
