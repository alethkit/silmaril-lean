module

public import Silmaril.SSA.SeaOfNodes.Pure.SubSelf.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SubSelf

open Diamond (Val ValueSort dataPorts)
open GVN (Producer)
open SubZero (model operands? word)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program rewritten : Program SubZero.Opcode inputs out}
variable {candidate : Producer program.dataflow word}

/-- Acceptance requires both actual operands to be the identical typed wire. -/
theorem fold_exact_source (accepted : fold? program candidate = some rewritten) :
    ∃ wire, operands? candidate = some (wire, wire) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.exact_source accepted

/-- The rewrite preserves the exact typed layout. -/
theorem fold_sigs (accepted : fold? program candidate = some rewritten) :
    rewritten.sigs = program.sigs :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.sigs_eq accepted

/-- All producer values agree at the original slots. -/
theorem fold_locals_eq (accepted : fold? program candidate = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    HEq (rewritten.dataflow.eval model entry PUnit.unit) (program.dataflow.eval model entry PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.locals_agree accepted entry

/-- An accepted fold preserves the typed native return for every input. -/
theorem fold_eval_eq (accepted : fold? program candidate = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    rewritten.eval model entry = program.eval model entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.eval_eq accepted entry

/-- A successful scan returns the result of the checked fold. -/
theorem step_checked (accepted : step? program = some rewritten) :
    ∃ candidate : Producer program.dataflow word, fold? program candidate = some rewritten := by
  obtain ⟨candidate, _, found⟩ := List.exists_of_findSome?_eq_some accepted
  exact ⟨candidate, found⟩

/-- A successful scan preserves the typed return for every input. -/
theorem step_eval_eq (accepted : step? program = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    rewritten.eval model entry = program.eval model entry := by
  obtain ⟨_, found⟩ := step_checked accepted
  exact fold_eval_eq found entry

end Silmaril.SSA.SeaOfNodes.Pure.SubSelf
