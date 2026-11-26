module

public import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass

open Diamond (Val ValueSort dataPorts)
open GVN (Producer)
open SubZero (BinaryOpcode model rewriteRightIdentity? word)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program next : Program SubZero.Opcode inputs out}

section Driver

variable (advance : Program SubZero.Opcode inputs out → Option (Program SubZero.Opcode inputs out))

/-- Observational equality composes through the bounded driver. -/
theorem runWith_eval_eq (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (preserves : ∀ {current next}, advance current = some next →
      ∀ (entry : Tuple (Val model.value) (dataPorts inputs)),
        next.eval model entry = current.eval model entry)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (runWith advance fuel program).program.eval model entry = program.eval model entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.runWith_eval_eq advance fuel program preserves entry

/-- One-binding steps give exact deletion and fuel accounting. -/
theorem runWith_progress (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (shrinks : ∀ {current next}, advance current = some next →
      next.sigs.length + 1 = current.sigs.length) :
    let final := runWith advance fuel program
    final.program.sigs.length + final.deletions = program.sigs.length ∧ final.deletions ≤ fuel :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.runWith_progress advance fuel program shrinks

/-- Initial table length suffices for a driver that removes one binding per step. -/
theorem runWith_stopped (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (shrinks : ∀ {current next}, advance current = some next →
      next.sigs.length + 1 = current.sigs.length) (enough : program.sigs.length ≤ fuel) :
    advance (runWith advance fuel program).program = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.runWith_stopped advance fuel program shrinks enough

end Driver

/-- Search failure excludes every nomination accepted by the shared checker. -/
theorem step?_eq_none_iff (program : Program SubZero.Opcode inputs out) :
    step? program = none ↔ Normal program :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.step_none_iff program

/-- A successful search returns the result of the shared checker. -/
theorem step_checked (accepted : step? program = some next) :
    ∃ (opcode : BinaryOpcode) (candidate source : Producer program.dataflow word),
      rewriteRightIdentity? opcode program candidate source = some next :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.step_checked accepted

/-- Every accepted step deletes exactly one binding. -/
theorem step_size (accepted : step? program = some next) :
    next.sigs.length + 1 = program.sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.step_size accepted

/-- A single step preserves the native result at every typed input. -/
theorem step_eval_eq (accepted : step? program = some next)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    next.eval model entry = program.eval model entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.step_eval_eq accepted entry

/-- A bounded run preserves the native result at every typed input. -/
theorem run_eval_eq (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (run fuel program).program.eval model entry = program.eval model entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.run_eval_eq fuel program entry

/-- The number of deletions is exact and bounded by the supplied fuel. -/
theorem run_progress (fuel : Nat) (program : Program SubZero.Opcode inputs out) :
    let final := run fuel program
    final.program.sigs.length + final.deletions = program.sigs.length ∧ final.deletions ≤ fuel :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.run_progress fuel program

/-- A run with fuel remaining has exhausted the shared matcher. -/
theorem run_normal_of_remaining (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (remaining : (run fuel program).deletions < fuel) : Normal (run fuel program).program :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.run_normal_of_remaining fuel program remaining

/-- The default fuel suffices to exhaust the matcher on the final table. -/
theorem normalize_normal (program : Program SubZero.Opcode inputs out) : Normal (normalize program).program :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.normalize_normal program

/-- Normalization preserves the native result at every typed input. -/
theorem normalize_eval_eq (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (normalize program).program.eval model entry = program.eval model entry :=
  run_eval_eq (program.sigs.length + 1) program entry

end Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass
