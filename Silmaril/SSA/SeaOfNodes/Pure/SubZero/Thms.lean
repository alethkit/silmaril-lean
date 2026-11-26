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
variable {candidate literal : Producer program.dataflow word} {opcode : BinaryOpcode}

/-- Acceptance witnesses the chosen operation and its exact right-hand
origin, which names the required literal. -/
theorem rightIdentity_exact_rhs
    (accepted : rewriteRightIdentity? opcode program candidate literal = some rewritten) :
    ∃ lhs rhs, operandsFor? opcode candidate = some (lhs, rhs) ∧
      isLiteral (rightIdentity opcode) literal = true ∧ inFinal candidate rhs = literal.origin :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.exact_rhs accepted

/-- A successful right-identity rewrite removes exactly one binding. -/
theorem rightIdentity_count
    (accepted : rewriteRightIdentity? opcode program candidate literal = some rewritten) :
    rewritten.sigs.length + 1 = program.sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.count accepted

/-- A successful right-identity rewrite preserves every native result. -/
theorem rightIdentity_eval_eq
    (accepted : rewriteRightIdentity? opcode program candidate literal = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    rewritten.eval model entry = program.eval model entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.eval accepted entry

variable {zero : Producer program.dataflow word}

/-- Acceptance witnesses the actual ordered subtraction and its exact typed
right-hand origin, which names a word-zero literal. -/
theorem rewrite_exact_rhs (accepted : rewrite? program candidate zero = some rewritten) :
    ∃ lhs rhs, operands? candidate = some (lhs, rhs) ∧ isZero zero = true ∧
      inFinal candidate rhs = zero.origin :=
  rightIdentity_exact_rhs accepted

/-- An accepted rewrite removes exactly the subtraction binding. -/
theorem rewrite_count (accepted : rewrite? program candidate zero = some rewritten) :
    rewritten.sigs.length + 1 = program.sigs.length :=
  rightIdentity_count accepted

/-- The native program returns exactly the same result at every typed input. -/
theorem rewrite_eval_eq (accepted : rewrite? program candidate zero = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    rewritten.eval model entry = program.eval model entry :=
  rightIdentity_eval_eq accepted entry

end Silmaril.SSA.SeaOfNodes.Pure.SubZero
