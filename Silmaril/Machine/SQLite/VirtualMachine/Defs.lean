module

public import Silmaril.Formats.Sqlite.Vdbe.Defs

/-! Fixed-code SQLite bytecode over a supplied snapshot of rowid tables.
The opcode reference is SQLite 3.54.1, https://www.sqlite.org/opcode.html,
at Fossil check-in
`555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The matching split source is
https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c.
-/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine

open Silmaril.Formats.Sqlite

abbrev Instruction := Vdbe.Instruction
abbrev Program := Vdbe.Program
abbrev Table := Vdbe.Table
abbrev Database := Vdbe.Database
abbrev State := Vdbe.State
abbrev Fault := Vdbe.Error
abbrev RunResult := Vdbe.RunResult

def initial : State := Vdbe.State.initial

abbrev step : Database → Program → State → Except Fault State := Vdbe.step

abbrev run : Database → Program → Nat → State → RunResult := Vdbe.run

/-- Zero-based column and instruction addresses. The bound key is an Int64
immediate. A missed seek jumps directly to the successful halt. -/
def pointProgram (database root column : Nat) (key : Int64) : Program :=
  #[.openRead 0 root database, .int64 key 1, .seekRowid 0 5 1,
    .column 0 column 2, .resultRow 2 1, .halt 0]

inductive Termination where
  | halted (code : Nat)
  | exhausted
  | fault (reason : Fault)
  deriving DecidableEq

/-- Rows in emission order, including rows emitted before exhaustion or fault. -/
structure Observation where
  rows : List (List Value)
  termination : Termination
  deriving DecidableEq

def observe : RunResult → Observation
  | .halted state =>
      ⟨state.rows, match state.halted with
        | some code => .halted code
        | none => .fault .alreadyHalted⟩
  | .exhausted state => ⟨state.rows, .exhausted⟩
  | .fault reason state => ⟨state.rows, .fault reason⟩

inductive PointError where
  | termination (status : Termination)
  | rowShape
  deriving DecidableEq

/-- A single SQL NULL cell is `ok (some .null)`. Only no rows yields
`ok none`. -/
def pointResult (obs : Observation) : Except PointError (Option Value) :=
  match obs.termination with
  | .halted 0 =>
      match obs.rows with
      | [] => .ok none
      | [[value]] => .ok (some value)
      | _ => .error .rowShape
  | status => .error (.termination status)

end Silmaril.Machine.SQLite.VirtualMachine
