module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison

open Diamond (Val ValueSort dataPorts)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Folding retains each original typed slot, including predicate slots. -/
theorem fold_sigs (program : Program Opcode inputs out) :
    (fold program).sigs = program.sigs := rfl

/-- Folding preserves all word and predicate producer values. -/
theorem fold_locals_eq (program : Program Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (fold program).dataflow.eval model entry PUnit.unit = program.dataflow.eval model entry PUnit.unit :=
  Scan.fold_locals_eq rules program entry

/-- Folding preserves the result at every typed input. -/
theorem fold_eval_eq (program : Program Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (fold program).eval model entry = program.eval model entry :=
  Scan.fold_eval_eq rules program entry

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison
