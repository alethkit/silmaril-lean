module

public import Silmaril.Formats.Sqlite.Vdbe.Defs
import Silmaril.Proofs.Formats.Sqlite.Vdbe

public section
namespace Silmaril.Formats.Sqlite.Vdbe

theorem execute_iff {database instruction before after} :
    execute database instruction before = .ok after ↔
      InstructionStep database instruction before after :=
  execute_iff_proof

theorem step_iff {database program before after} :
    step database program before = .ok after ↔ Step database program before after :=
  step_iff_proof

theorem run_trace (database : Database) (program : Program) (fuel : Nat) (before : State) :
    Trace database program before (run database program fuel before).state :=
  run_trace_proof database program fuel before

end Silmaril.Formats.Sqlite.Vdbe
