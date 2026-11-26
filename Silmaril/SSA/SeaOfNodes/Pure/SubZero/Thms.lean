module

public import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SubZero

open Diamond (Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (inFinal)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program rewritten : Program Opcode inputs out}
variable {candidate zero : Producer program.dataflow word}

/-- Acceptance witnesses the actual ordered subtraction and its exact typed
right-hand origin, which names a word-zero literal. -/
theorem rewrite_exact_rhs (accepted : rewrite? program candidate zero = some rewritten) :
    ∃ lhs rhs, operands? candidate = some (lhs, rhs) ∧ isZero zero = true ∧
      inFinal candidate rhs = zero.origin :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.old_rhs accepted

/-- An accepted rewrite removes exactly the subtraction binding. -/
theorem rewrite_count (accepted : rewrite? program candidate zero = some rewritten) :
    rewritten.sigs.length + 1 = program.sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.count accepted

/-- The native program returns exactly the same result at every typed input. -/
theorem rewrite_eval_eq (accepted : rewrite? program candidate zero = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    rewritten.eval model entry = program.eval model entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.eval accepted entry

end Silmaril.SSA.SeaOfNodes.Pure.SubZero
