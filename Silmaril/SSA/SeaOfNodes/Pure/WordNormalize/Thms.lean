module

public import Silmaril.SSA.SeaOfNodes.Pure.WordNormalize.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.Correctness
import Silmaril.SSA.SeaOfNodes.Pure.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.WordNormalize

open Diamond (Val ValueSort dataPorts)
open SubZero (model)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program next : Program SubZero.Opcode inputs out}

/-- Search stops exactly when both matchers reject the current table. -/
theorem step?_eq_none_iff (program : Program SubZero.Opcode inputs out) :
    step? program = none ↔ Normal program :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.step_none_iff program

/-- Either kind of successful step deletes exactly one binding. -/
theorem step_size (accepted : step? program = some next) :
    next.sigs.length + 1 = program.sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.step_size accepted

/-- Either kind of successful step preserves the return. -/
theorem step_eval_eq (accepted : step? program = some next)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    next.eval model entry = program.eval model entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.step_eval_eq accepted entry

/-- The deletion count is exact and bounded by the original table length. -/
theorem normalize_count (program : Program SubZero.Opcode inputs out) :
    let final := normalize program
    final.program.sigs.length + final.deletions = program.sigs.length ∧
      final.deletions ≤ program.sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.normalize_count program

/-- The final program has neither supported match. -/
theorem normalize_normal (program : Program SubZero.Opcode inputs out) :
    Normal (normalize program).program :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.normalize_normal program

/-- Normalization preserves the native return at every typed input. -/
theorem normalize_eval_eq (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (normalize program).program.eval model entry = program.eval model entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.normalize_eval_eq program entry

/-- The existing RVSDG emission observes the same singleton return. -/
theorem normalize_lower_run_eq (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (normalize program).program.lower.run (toRVSDGModel model) entry =
      program.lower.run (toRVSDGModel model) entry := by
  rw [(normalize program).program.lower_run, program.lower_run, normalize_eval_eq program entry]

end Silmaril.SSA.SeaOfNodes.Pure.WordNormalize
