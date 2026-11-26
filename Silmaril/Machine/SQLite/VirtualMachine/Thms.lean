module

public import Silmaril.Machine.SQLite.VirtualMachine.Defs
public import Silmaril.Formats.Sqlite.Vdbe.Thms

public section

namespace Silmaril.Machine.SQLite.VirtualMachine

open Silmaril.Formats.Sqlite

theorem step_iff {database program before after} :
    step database program before = .ok after ↔ Vdbe.Step database program before after :=
  Vdbe.step_iff

theorem run_trace (database : Database) (program : Program) (fuel : Nat) (before : State) :
    Vdbe.Trace database program before (run database program fuel before).state :=
  Vdbe.run_trace database program fuel before

end Silmaril.Machine.SQLite.VirtualMachine
