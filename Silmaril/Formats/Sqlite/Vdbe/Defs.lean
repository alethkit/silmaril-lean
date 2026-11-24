module
public import Silmaril.Formats.Sqlite.BTree.Query.ReadModel.Defs
public import Silmaril.Formats.Sqlite.Defs

/-! A read-only VDBE core with explicit program counters, registers and cursors.
Raw bytecode representation is unrestricted. Executability is a separate,
partial lowering into documented scalar and rowid-table opcodes. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.Vdbe

abbrev Table := BTree.Query.ReadModel Int (List Value)
abbrev Database := Nat → Nat → Option Table

inductive Instruction where
  | init (target : Nat)
  | goto (target : Nat)
  | halt (code : Nat)
  | integer (value : Int32) (destination : Nat)
  | int64 (value : Int64) (destination : Nat)
  | string8 (value : String) (destination : Nat)
  | null (first last : Nat)
  | copy (source destination additional : Nat)
  | openRead (cursor root database : Nat)
  | rewind (cursor emptyTarget : Nat)
  | next (cursor loopTarget : Nat)
  | column (cursor column destination : Nat)
  | rowid (cursor destination : Nat)
  | resultRow (first count : Nat)
  | seekRowid (cursor missingTarget keyRegister : Nat)
  deriving DecidableEq

abbrev Program := Array Instruction

/-- Numeric opcode identities depend on the SQLite build. Named opcodes can
be interpreted without silently guessing that build-specific numbering. -/
inductive RawOpcode where
  | number (code : Nat)
  | name (name : String)
  | identified (code : Nat) (name : String)
  deriving DecidableEq

inductive P4 where
  | none
  | text (value : String)
  | integer (value : Int)
  | real (bits : UInt64)
  | blob (value : Silmaril.Formats.Bytes)
  | pointer (address : Nat)
  | opaque (tag : String) (payload : Silmaril.Formats.Bytes)
  deriving DecidableEq

structure RawInstruction where
  opcode : RawOpcode
  p1 : Int := 0
  p2 : Int := 0
  p3 : Int := 0
  p4 : P4 := .none
  p5 : Nat := 0
  deriving DecidableEq

abbrev RawProgram := Array RawInstruction

structure Variant where
  allows : Instruction → Bool

def Variant.scalar : Variant := ⟨fun instruction => match instruction with
  | .openRead .. | .rewind .. | .next .. | .column .. | .rowid .. | .seekRowid .. => false
  | _ => true⟩

def Variant.readOnly : Variant := ⟨fun _ => true⟩

def RawOpcode.name? : RawOpcode → Option String
  | .number _ => none
  | .name text | .identified _ text => some text

def operand? (value : Int) : Option Nat :=
  if value < 0 then none else some value.toNat

def register? (value : Int) : Option Nat :=
  if value ≤ 0 then none else some value.toNat

def signed32 (value : Int) : Bool := decide (-(2^31 : Int) ≤ value ∧ value < 2^31)

/-- Decode the default flags of a pinned opcode subset. P4 text is the decoded
UTF-8 constant up to its terminating NUL. Pointer-bearing/index modes are not
accepted. The raw input remains available even when lowering fails. -/
def decode? (raw : RawInstruction) : Option Instruction := do
  if raw.p5 != 0 then none else do
    let name ← raw.opcode.name?
    if raw.p4 != .none && name != "Int64" && name != "String8" && name != "OpenRead" then none else do
    match name with
    | "Init" =>
        if raw.p1 != 0 || raw.p3 != 0 || raw.p4 != .none then none
        else return .init (← operand? raw.p2)
    | "Goto" => return .goto (← operand? raw.p2)
    | "Halt" =>
        if raw.p2 != 0 || raw.p3 != 0 || raw.p4 != .none then none
        else return .halt (← operand? raw.p1)
    | "Integer" =>
        if !signed32 raw.p1 then none else
          return .integer (Int32.ofInt raw.p1) (← register? raw.p2)
    | "Int64" =>
        match raw.p4 with
        | .integer value =>
            if raw.p1 != 0 || raw.p3 != 0 ||
                !(decide (-(2^63 : Int) ≤ value ∧ value < 2^63)) then none
            else return .int64 (Int64.ofInt value) (← register? raw.p2)
        | .none =>
            if !signed32 raw.p1 || !signed32 raw.p3 then none else
              let low := (Int32.ofInt raw.p1).toUInt32.toUInt64
              let high := (Int32.ofInt raw.p3).toUInt32.toUInt64
              return .int64 (low ||| (high <<< 32)).toInt64 (← register? raw.p2)
        | _ => none
    | "String8" =>
        match raw.p4 with
        | .text text =>
            if raw.p3 != 0 || text.contains '\x00' then none
            else return .string8 text (← register? raw.p2)
        | _ => none
    | "Null" =>
        if raw.p1 != 0 then none else return .null (← register? raw.p2) (← operand? raw.p3)
    | "Copy" =>
        if raw.p1 = raw.p2 then none else
          return .copy (← register? raw.p1) (← register? raw.p2) (← operand? raw.p3)
    | "OpenRead" =>
        match raw.p4 with
        | .none =>
            return .openRead (← operand? raw.p1) (← register? raw.p2) (← operand? raw.p3)
        | .integer count =>
            if count < 0 then none else
              return .openRead (← operand? raw.p1) (← register? raw.p2) (← operand? raw.p3)
        | _ => none
    | "Rewind" => return .rewind (← operand? raw.p1) (← operand? raw.p2)
    | "Next" =>
        if raw.p3 != 0 then none else return .next (← operand? raw.p1) (← operand? raw.p2)
    | "Column" =>
        if raw.p4 != .none then none else
          return .column (← operand? raw.p1) (← operand? raw.p2) (← register? raw.p3)
    | "Rowid" => return .rowid (← operand? raw.p1) (← register? raw.p2)
    | "ResultRow" => return .resultRow (← register? raw.p1) (← operand? raw.p2)
    | "SeekRowid" => return .seekRowid (← operand? raw.p1) (← operand? raw.p2) (← register? raw.p3)
    | _ => none

inductive Lowered where
  | supported (instruction : Instruction)
  | unsupported (raw : RawInstruction)
  deriving DecidableEq

def lower (variant : Variant) (raw : RawInstruction) : Lowered :=
  match decode? raw with
  | some instruction => if variant.allows instruction then .supported instruction else .unsupported raw
  | none => .unsupported raw

def lowerProgram (variant : Variant) (program : RawProgram) : Array Lowered := program.map (lower variant)

def lowerProgram? (variant : Variant) (program : RawProgram) : Option Program :=
  program.mapM fun raw => match lower variant raw with
    | .supported instruction => some instruction
    | .unsupported _ => none

structure Cursor where
  table : Table
  /-- `none` means not positioned; `some []` means end of scan. -/
  remaining : Option (List (Int × List Value)) := none
  /-- SeekRowid does not establish the forward scan precondition of Next. -/
  forward : Bool := false

def Cursor.current? (cursor : Cursor) : Option (Int × List Value) :=
  cursor.remaining.bind List.head?

structure State where
  pc : Nat := 0
  registers : Nat → Value := fun _ => .null
  cursors : Nat → Option Cursor := fun _ => none
  rows : List (List Value) := []
  halted : Option Nat := none

def State.initial : State := {}
def State.advance (state : State) : State := {state with pc := state.pc + 1}
def State.jump (state : State) (target : Nat) : State := {state with pc := target}
def State.write (state : State) (register : Nat) (value : Value) : State :=
  {state with registers := fun index => if index = register then value else state.registers index}
def State.setCursor (state : State) (identifier : Nat) (cursor : Cursor) : State :=
  {state with cursors := fun index => if index = identifier then some cursor else state.cursors index}
def State.writeNull (state : State) (first last : Nat) : State :=
  {state with registers := fun index =>
    if first ≤ index ∧ index ≤ max first last then .null else state.registers index}

/-- Sequential forward copying, matching the documented P3+1 register count. -/
def State.copyRegisters : Nat → Nat → Nat → State → State
  | 0, _, _, state => state
  | count + 1, source, destination, state =>
      copyRegisters count (source + 1) (destination + 1)
        (state.write destination (state.registers source))

def State.emit (state : State) (first count : Nat) : State :=
  {state with rows := state.rows ++ [(List.range count).map (fun offset => state.registers (first + offset))]}

def State.rewindCursor (state : State) (identifier target : Nat) (cursor : Cursor) : State :=
  (state.setCursor identifier {cursor with remaining := some cursor.table.entries, forward := true}).jump
    (if cursor.table.entries.isEmpty then target else state.pc + 1)

def State.nextCursor (state : State) (identifier target : Nat) (cursor : Cursor)
    (remaining : List (Int × List Value)) : State :=
  (state.setCursor identifier {cursor with remaining := some remaining.tail}).jump
    (if remaining.tail.isEmpty then state.pc + 1 else target)

def State.seekCursor (state : State) (identifier target : Nat) (cursor : Cursor) (key : Int64) : State :=
  let remaining := cursor.table.entries.dropWhile (fun entry => entry.1 != key.toInt)
  (state.setCursor identifier {cursor with remaining := some remaining, forward := false}).jump
    (if remaining.isEmpty then target else state.pc + 1)

inductive Error where
  | programCounter (address : Nat)
  | alreadyHalted
  | missingTable (database root : Nat)
  | missingCursor (cursor : Nat)
  | unpositionedCursor (cursor : Nat)
  | noCurrentRow (cursor : Nat)
  | emptyRewindAssertion
  | missingSeekAssertion
  | invalidAdvance
  | rowidRange (key : Int)
  | unsupportedSeekKey
  deriving DecidableEq

def execute (database : Database) (instruction : Instruction) (state : State) : Except Error State :=
  match instruction with
  | .init target => .ok (state.jump (if target = 0 then state.pc + 1 else target))
  | .goto target => .ok (state.jump target)
  | .halt code => .ok {state with halted := some code}
  | .integer value destination => .ok ((state.write destination (.integer value.toInt64)).advance)
  | .int64 value destination => .ok ((state.write destination (.integer value)).advance)
  | .string8 value destination => .ok ((state.write destination (.text value)).advance)
  | .null first last => .ok ((state.writeNull first last).advance)
  | .copy source destination additional =>
      .ok ((State.copyRegisters (additional + 1) source destination state).advance)
  | .openRead identifier root databaseId =>
      match database databaseId root with
      | none => .error (.missingTable databaseId root)
      | some table => .ok ((state.setCursor identifier {table := table}).advance)
  | .rewind identifier target =>
      match state.cursors identifier with
      | none => .error (.missingCursor identifier)
      | some cursor =>
          if cursor.table.entries.isEmpty = true ∧ target = 0 then .error .emptyRewindAssertion
          else .ok (state.rewindCursor identifier target cursor)
  | .next identifier target =>
      match state.cursors identifier with
      | none => .error (.missingCursor identifier)
      | some cursor => if cursor.forward = false then .error .invalidAdvance else match cursor.remaining with
          | none => .error (.unpositionedCursor identifier)
          | some remaining => .ok (state.nextCursor identifier target cursor remaining)
  | .column identifier column destination =>
      match state.cursors identifier with
      | none => .error (.missingCursor identifier)
      | some cursor => match cursor.current? with
          | none => .error (.noCurrentRow identifier)
          | some entry => .ok ((state.write destination (entry.2[column]?.getD .null)).advance)
  | .rowid identifier destination =>
      match state.cursors identifier with
      | none => .error (.missingCursor identifier)
      | some cursor => match cursor.current? with
          | none => .error (.noCurrentRow identifier)
          | some entry =>
              if -(2^63 : Int) ≤ entry.1 ∧ entry.1 < 2^63 then
                .ok ((state.write destination (.integer (Int64.ofInt entry.1))).advance)
              else .error (.rowidRange entry.1)
  | .resultRow first count => .ok ((state.emit first count).advance)
  | .seekRowid identifier target register =>
      match state.cursors identifier with
      | none => .error (.missingCursor identifier)
      | some cursor => match state.registers register with
          | .integer key =>
              if (cursor.table.entries.dropWhile (fun entry => entry.1 != key.toInt)).isEmpty = true ∧ target = 0
              then .error .missingSeekAssertion
              else .ok (state.seekCursor identifier target cursor key)
          | _ => .error .unsupportedSeekKey

/-- Independent instruction semantics: each constructor gives the state
transformation and its premises, without calling the interpreter. -/
inductive InstructionStep (database : Database) : Instruction → State → State → Prop where
  | init (s target) : InstructionStep database (.init target) s
      (s.jump (if target = 0 then s.pc + 1 else target))
  | goto (s target) : InstructionStep database (.goto target) s (s.jump target)
  | halt (s code) : InstructionStep database (.halt code) s {s with halted := some code}
  | integer (s value destination) : InstructionStep database (.integer value destination) s
      ((s.write destination (.integer value.toInt64)).advance)
  | int64 (s value destination) : InstructionStep database (.int64 value destination) s
      ((s.write destination (.integer value)).advance)
  | string8 (s value destination) : InstructionStep database (.string8 value destination) s
      ((s.write destination (.text value)).advance)
  | null (s first last) : InstructionStep database (.null first last) s ((s.writeNull first last).advance)
  | copy (s source destination additional) : InstructionStep database (.copy source destination additional) s
      ((State.copyRegisters (additional + 1) source destination s).advance)
  | openRead {s identifier root databaseId table} (found : database databaseId root = some table) :
      InstructionStep database (.openRead identifier root databaseId) s
        ((s.setCursor identifier {table := table}).advance)
  | rewind {s identifier target cursor} (found : s.cursors identifier = some cursor)
      (valid : ¬(cursor.table.entries.isEmpty = true ∧ target = 0)) :
      InstructionStep database (.rewind identifier target) s (s.rewindCursor identifier target cursor)
  | next {s identifier target cursor remaining} (found : s.cursors identifier = some cursor)
      (forward : cursor.forward ≠ false)
      (positioned : cursor.remaining = some remaining) :
      InstructionStep database (.next identifier target) s (s.nextCursor identifier target cursor remaining)
  | column {s identifier column destination cursor entry} (found : s.cursors identifier = some cursor)
      (current : cursor.current? = some entry) :
      InstructionStep database (.column identifier column destination) s
        ((s.write destination (entry.2[column]?.getD .null)).advance)
  | rowid {s identifier destination cursor entry} (found : s.cursors identifier = some cursor)
      (current : cursor.current? = some entry) (range : -(2^63 : Int) ≤ entry.1 ∧ entry.1 < 2^63) :
      InstructionStep database (.rowid identifier destination) s
        ((s.write destination (.integer (Int64.ofInt entry.1))).advance)
  | resultRow (s first count) : InstructionStep database (.resultRow first count) s ((s.emit first count).advance)
  | seekRowid {s identifier target register cursor key} (found : s.cursors identifier = some cursor)
      (integer : s.registers register = .integer key)
      (valid : ¬((cursor.table.entries.dropWhile (fun entry => entry.1 != key.toInt)).isEmpty = true ∧ target = 0)) :
      InstructionStep database (.seekRowid identifier target register) s (s.seekCursor identifier target cursor key)

def step (database : Database) (program : Program) (state : State) : Except Error State :=
  if state.halted.isSome then .error .alreadyHalted else
    match program[state.pc]? with
    | none => .error (.programCounter state.pc)
    | some instruction => execute database instruction state

inductive Step (database : Database) (program : Program) : State → State → Prop where
  | instruction {before after instruction} (active : before.halted = none)
      (fetch : program[before.pc]? = some instruction)
      (transition : InstructionStep database instruction before after) : Step database program before after

inductive Trace (database : Database) (program : Program) : State → State → Prop where
  | refl (state) : Trace database program state state
  | cons {before middle after} : Step database program before middle →
      Trace database program middle after → Trace database program before after

inductive RunResult where
  | halted (state : State)
  | exhausted (state : State)
  | fault (error : Error) (state : State)

def RunResult.state : RunResult → State
  | .halted state | .exhausted state | .fault _ state => state

def run (database : Database) (program : Program) : Nat → State → RunResult
  | fuel, state =>
      if state.halted.isSome then .halted state else
        match fuel with
        | 0 => .exhausted state
        | fuel + 1 => match step database program state with
            | .error error => .fault error state
            | .ok next => run database program fuel next

end Silmaril.Formats.Sqlite.Vdbe
