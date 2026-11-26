module

import Silmaril.Machine.SQLite.VirtualMachine.Isolation.Thms

/-! Non-vacuity checks, concrete allowed/rejected examples, unguarded-effect
counterexamples, and axiom guards for `VirtualMachine.Isolation`. -/

namespace Silmaril.Machine.SQLite.VirtualMachine.Isolation.Checks

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine
open Silmaril.Machine.SQLite.VirtualMachine.Isolation

private def samplePolicy : Policy := Policy.mainDbOnly 4 2 2

private def sampleTable : Table :=
  BTree.Query.ReadModel.ofList
    [(1, [.text "alice"]), (2, [.text "bob"])]

private def sampleHost : HostState where
  databases := fun db root =>
    if db = 0 ∧ root = 2 then some sampleTable else none

/-- Legitimate read-only table-scan program in raw VDBE form:
`OpenRead 0 2 0; Rewind 0 5; Column 0 0 1; ResultRow 1 1; Next 0 2; Halt 0`. -/
private def scanRawProgram : Vdbe.RawProgram :=
  #[ { opcode := .name "OpenRead", p1 := 0, p2 := 2, p3 := 0 },
     { opcode := .name "Rewind", p1 := 0, p2 := 5 },
     { opcode := .name "Column", p1 := 0, p2 := 0, p3 := 1 },
     { opcode := .name "ResultRow", p1 := 1, p2 := 1 },
     { opcode := .name "Next", p1 := 0, p2 := 2 },
     { opcode := .name "Halt", p1 := 0 } ]

private def expectedScanProgram : Program :=
  #[ .openRead 0 2 0,
     .rewind 0 5,
     .column 0 0 1,
     .resultRow 1 1,
     .next 0 2,
     .halt 0 ]

/-- Positive non-vacuity: the scan program is admitted by `samplePolicy`. -/
example : admitProgram samplePolicy scanRawProgram = .ok expectedScanProgram := rfl

/-- Positive non-vacuity: executing the admitted scan program reads table `(0, 2)`,
emits both rows, halts cleanly with code 0, and leaves `sampleHost` unchanged. -/
example :
    match admitAndRun samplePolicy sampleHost scanRawProgram 16 with
    | .executed out =>
        out.events = [.readTable 0 2 true, .emitRow [.text "alice"], .emitRow [.text "bob"]] ∧
        observe out.result = ⟨[[.text "alice"], [.text "bob"]], .halted 0⟩ ∧
        out.host.attached = [] ∧
        out.host.extensions = [] ∧
        out.host.writeCount = 0
    | .rejected _ => False :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Safe runtime rejection: an admitted program opening a missing authorized
table faults cleanly with `.missingTable` and emits only an allowed read event. -/
private def missingTableRaw : Vdbe.RawProgram :=
  #[ { opcode := .name "OpenRead", p1 := 0, p2 := 99, p3 := 0 },
     { opcode := .name "Halt", p1 := 0 } ]

example :
    match admitAndRun samplePolicy sampleHost missingTableRaw 4 with
    | .executed out =>
        out.events = [.readTable 0 99 false] ∧
        observe out.result = ⟨[], .fault (.missingTable 0 99)⟩
    | .rejected _ => False :=
  ⟨rfl, rfl⟩

/-- Denied write opcode (`OpenWrite`) is rejected before execution. -/
private def openWriteInstr : RawInstruction :=
  { opcode := .name "OpenWrite", p1 := 0, p2 := 2, p3 := 0 }

example : admitProgram samplePolicy #[openWriteInstr, { opcode := .name "Halt" }] =
    .error (.deniedOpcode "OpenWrite") := rfl

/-- Counterexample without the admission gate: `openWriteInstr` carries a
disallowed `writeTable` host effect. -/
example :
    ∃ e, rawPotentialEffect openWriteInstr = some e ∧ ¬ e.Allowed samplePolicy :=
  ⟨.writeTable 0 2, rfl, not_allowed_writeTable samplePolicy 0 2⟩

/-- Denied `Attach` opcode is rejected before execution and carries a disallowed
`attachDb` effect without the gate. -/
private def attachInstr : RawInstruction :=
  { opcode := .name "Attach", p4 := .text "other.db" }

example : admitProgram samplePolicy #[attachInstr] = .error (.deniedOpcode "Attach") := rfl

example :
    ∃ e, rawPotentialEffect attachInstr = some e ∧ ¬ e.Allowed samplePolicy :=
  ⟨.attachDb "other.db", rfl, not_allowed_attachDb samplePolicy "other.db"⟩

/-- Denied `LoadExtension` opcode is rejected before execution and carries a
disallowed `loadExtension` effect without the gate. -/
private def loadExtInstr : RawInstruction :=
  { opcode := .name "LoadExtension", p4 := .text "evil.so" }

example : admitProgram samplePolicy #[loadExtInstr] =
    .error (.deniedOpcode "LoadExtension") := rfl

example :
    ∃ e, rawPotentialEffect loadExtInstr = some e ∧ ¬ e.Allowed samplePolicy :=
  ⟨.loadExtension "evil.so", rfl, not_allowed_loadExtension samplePolicy "evil.so"⟩

/-- Unknown numeric opcode is rejected as unsupported. -/
private def unknownNumericInstr : RawInstruction :=
  { opcode := .number 999 }

example : admitProgram samplePolicy #[unknownNumericInstr] =
    .error (.unsupportedOpcode unknownNumericInstr) := rfl

/-- Unauthorized database id (`db = 1` under `mainDbOnly`) is rejected. -/
example :
    admitProgram samplePolicy #[{ opcode := .name "OpenRead", p1 := 0, p2 := 2, p3 := 1 }] =
      .error (.disallowedDatabase 1 2) := rfl

/-- Out-of-bounds register write is rejected. -/
example :
    admitProgram samplePolicy #[{ opcode := .name "Integer", p1 := 42, p2 := 5 }] =
      .error (.registerOutOfBounds 5 4) := rfl

/-- Out-of-bounds cursor open is rejected. -/
example :
    admitProgram samplePolicy #[{ opcode := .name "OpenRead", p1 := 2, p2 := 2, p3 := 0 }] =
      .error (.cursorOutOfBounds 2 2) := rfl

/-- Excessive result row width is rejected. -/
example :
    admitProgram samplePolicy #[{ opcode := .name "ResultRow", p1 := 1, p2 := 3 }] =
      .error (.resultWidthExceeded 3 2) := rfl

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.admitProgram_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.admitProgram_wellFormed

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.stepIsolated_isolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.stepIsolated_isolation

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.runIsolated_isolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.runIsolated_isolation

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.admitAndRun_isolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.admitAndRun_isolation

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.admitAndRun_no_denied_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.admitAndRun_no_denied_effects

end Silmaril.Machine.SQLite.VirtualMachine.Isolation.Checks
