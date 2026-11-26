module

public import Silmaril.Machine.SQLite.VirtualMachine.Defs

/-! High-level read-only isolation model for the Silmaril SQLite VDBE VM.

This module extends the existing read-only VDBE core
(`Silmaril.Formats.Sqlite.Vdbe.Defs` and `Silmaril.Machine.SQLite.VirtualMachine.Defs`)
with:
1. A capability and resource-bound policy (`Policy`) governing authorized
   `(database, root)` reads, register bounds, cursor bounds, and result row width.
2. An explicit host state (`HostState`) and effect alphabet (`Effect`) that
   includes both allowed read-only effects (`readTable`, `emitRow`) and denied
   mutation/escape effects (`writeTable`, `attachDb`, `loadExtension`, `hostEscape`).
3. A static admission gate (`admitProgram`) over arbitrary untrusted raw bytecode
   (`Vdbe.RawProgram`) that explicitly rejects denied write/attach/extension
   opcodes, unknown/flag-bearing opcodes, disallowed database accesses, and
   out-of-bounds operands, admitting only `WellFormed` read-only programs.
4. Per-step and finite-prefix isolated execution (`stepIsolated`, `runIsolated`,
   `admitAndRun`) whose VM state transitions agree with `VirtualMachine.step` /
   `VirtualMachine.run` while preserving `HostState` and `StateInv`.

Scope and limits:
- Single connection, single thread, high-level abstract VDBE semantics.
- Covers safety, allowed host effects, host immutability, cursor provenance,
  register/row-width confinement, and safe pre-execution or runtime rejection.
- Does NOT prove confidentiality/noninterference, termination, blanket step/memory
  resource caps, query-result correctness, SQL compiler postconditions, or C/ELF
  refinement of `libsqlite3.so`.
- Designed to compose in future work with `VirtualMachine.Traced` / ITree host
  effect handlers and dynamic subprogram/trigger closure once those layers are
  connected.
-/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Isolation

open Silmaril.Formats.Sqlite

/-- Read-only host capability and operand-bound policy for an isolated
single-connection SQLite VM execution. -/
structure Policy where
  /-- Authorizes `(database, root)` pairs that `OpenRead` may access. -/
  canRead : Nat → Nat → Bool
  /-- Upper bound on accessed register indices (`1 ≤ r ≤ maxRegisters`). -/
  maxRegisters : Nat
  /-- Strict upper bound on cursor identifiers (`cursor < maxCursors`). -/
  maxCursors : Nat
  /-- Upper bound on the column width of any `ResultRow`. -/
  maxResultWidth : Nat

/-- Standard single-database read-only policy permitting reads only on `main`
(database id `0`) within the given register, cursor, and row-width bounds. -/
def Policy.mainDbOnly (maxRegisters maxCursors maxResultWidth : Nat) : Policy where
  canRead := fun db _ => db == 0
  maxRegisters := maxRegisters
  maxCursors := maxCursors
  maxResultWidth := maxResultWidth

/-- Abstract host/environment state outside the VM's registers and cursors.
`databases` holds the protected read-only table snapshots; `attached`,
`extensions`, and `writeCount` model host surfaces that must remain unchanged
across any isolated read-only run. -/
structure HostState where
  databases : Database
  attached : List String := []
  extensions : List String := []
  writeCount : Nat := 0

/-- Observable VM-to-host effect events. Both read-only effects and denied
mutation/attach/extension/escape effects are representable in this alphabet so
that allowed-effect isolation theorems are non-tautological. -/
inductive Effect where
  | readTable (database root : Nat) (found : Bool)
  | emitRow (cells : List Value)
  | writeTable (database root : Nat)
  | attachDb (name : String)
  | loadExtension (path : String)
  | hostEscape (opcode : String)
  deriving DecidableEq

/-- Policy-authorized effect predicate. Only authorized table reads and bounded
result rows are allowed; write, attach, extension, and escape effects are
unconditionally denied. -/
def Effect.Allowed (policy : Policy) : Effect → Prop
  | .readTable db root _ => policy.canRead db root = true
  | .emitRow cells => cells.length ≤ policy.maxResultWidth
  | .writeTable _ _ => False
  | .attachDb _ => False
  | .loadExtension _ => False
  | .hostEscape _ => False

/-- Decidable boolean check corresponding to `Effect.Allowed`. -/
def Effect.isAllowed (policy : Policy) : Effect → Bool
  | .readTable db root _ => policy.canRead db root
  | .emitRow cells => decide (cells.length ≤ policy.maxResultWidth)
  | .writeTable _ _ => false
  | .attachDb _ => false
  | .loadExtension _ => false
  | .hostEscape _ => false

/-- Known mutating, attach, subprogram, or host-extension SQLite VDBE opcode
names explicitly classified as denied by the read-only profile. Any other
unmodeled opcode is still rejected as `unsupportedOpcode`. -/
def deniedOpcodeNames : List String :=
  [ "OpenWrite", "Insert", "InsertInt", "Delete", "NewRowid",
    "CreateBtree", "Clear", "Destroy", "DropTable", "DropIndex", "DropTrigger",
    "Transaction", "WriteCookie", "SetCookie", "Savepoint",
    "Attach", "Detach", "LoadExtension", "VUpdate", "VCreate", "VDestroy",
    "Program", "Function", "PureFunc" ]

/-- Explicit reasons for rejecting an untrusted `RawProgram` before execution. -/
inductive RejectionReason where
  | deniedOpcode (name : String)
  | unsupportedOpcode (raw : RawInstruction)
  | disallowedDatabase (database root : Nat)
  | registerOutOfBounds (register maxRegisters : Nat)
  | cursorOutOfBounds (cursor maxCursors : Nat)
  | resultWidthExceeded (count maxResultWidth : Nat)
  | branchTargetOutOfBounds (target codeSize : Nat)
  deriving DecidableEq

/-- Static well-formedness and capability-conformance predicate for a single
lowered VDBE instruction within a program of length `codeSize`. -/
def InstructionWf (policy : Policy) (codeSize : Nat) : Instruction → Prop
  | .init target => target = 0 ∨ target < codeSize
  | .goto target => target < codeSize
  | .halt _ => True
  | .integer _ destination => 1 ≤ destination ∧ destination ≤ policy.maxRegisters
  | .int64 _ destination => 1 ≤ destination ∧ destination ≤ policy.maxRegisters
  | .string8 _ destination => 1 ≤ destination ∧ destination ≤ policy.maxRegisters
  | .null first last => 1 ≤ first ∧ max first last ≤ policy.maxRegisters
  | .copy source destination additional =>
      1 ≤ source ∧ source + additional ≤ policy.maxRegisters ∧
      1 ≤ destination ∧ destination + additional ≤ policy.maxRegisters
  | .openRead cursor root database =>
      policy.canRead database root = true ∧ cursor < policy.maxCursors
  | .rewind cursor emptyTarget =>
      cursor < policy.maxCursors ∧ (emptyTarget = 0 ∨ emptyTarget < codeSize)
  | .next cursor loopTarget =>
      cursor < policy.maxCursors ∧ loopTarget < codeSize
  | .column cursor _ destination =>
      cursor < policy.maxCursors ∧ 1 ≤ destination ∧ destination ≤ policy.maxRegisters
  | .rowid cursor destination =>
      cursor < policy.maxCursors ∧ 1 ≤ destination ∧ destination ≤ policy.maxRegisters
  | .resultRow first count =>
      count ≤ policy.maxResultWidth ∧
      (count = 0 ∨ (1 ≤ first ∧ first + count - 1 ≤ policy.maxRegisters))
  | .seekRowid cursor missingTarget keyRegister =>
      cursor < policy.maxCursors ∧
      (missingTarget = 0 ∨ missingTarget < codeSize) ∧
      1 ≤ keyRegister ∧ keyRegister ≤ policy.maxRegisters

/-- Executable capability and well-formedness checker for one lowered
instruction. -/
def checkInstruction (policy : Policy) (codeSize : Nat) (instr : Instruction) :
    Except RejectionReason Unit :=
  match instr with
  | .init target =>
      if target = 0 ∨ target < codeSize then .ok ()
      else .error (.branchTargetOutOfBounds target codeSize)
  | .goto target =>
      if target < codeSize then .ok ()
      else .error (.branchTargetOutOfBounds target codeSize)
  | .halt _ => .ok ()
  | .integer _ destination | .int64 _ destination | .string8 _ destination =>
      if 1 ≤ destination ∧ destination ≤ policy.maxRegisters then .ok ()
      else .error (.registerOutOfBounds destination policy.maxRegisters)
  | .null first last =>
      if 1 ≤ first ∧ max first last ≤ policy.maxRegisters then .ok ()
      else .error (.registerOutOfBounds (if first = 0 then 0 else max first last) policy.maxRegisters)
  | .copy source destination additional =>
      if !(1 ≤ source ∧ source + additional ≤ policy.maxRegisters) then
        .error (.registerOutOfBounds (if source = 0 then 0 else source + additional) policy.maxRegisters)
      else if !(1 ≤ destination ∧ destination + additional ≤ policy.maxRegisters) then
        .error (.registerOutOfBounds (if destination = 0 then 0 else destination + additional) policy.maxRegisters)
      else .ok ()
  | .openRead cursor root database =>
      if policy.canRead database root = false then
        .error (.disallowedDatabase database root)
      else if !(cursor < policy.maxCursors) then
        .error (.cursorOutOfBounds cursor policy.maxCursors)
      else .ok ()
  | .rewind cursor emptyTarget =>
      if !(cursor < policy.maxCursors) then
        .error (.cursorOutOfBounds cursor policy.maxCursors)
      else if !(emptyTarget = 0 ∨ emptyTarget < codeSize) then
        .error (.branchTargetOutOfBounds emptyTarget codeSize)
      else .ok ()
  | .next cursor loopTarget =>
      if !(cursor < policy.maxCursors) then
        .error (.cursorOutOfBounds cursor policy.maxCursors)
      else if !(loopTarget < codeSize) then
        .error (.branchTargetOutOfBounds loopTarget codeSize)
      else .ok ()
  | .column cursor _ destination | .rowid cursor destination =>
      if !(cursor < policy.maxCursors) then
        .error (.cursorOutOfBounds cursor policy.maxCursors)
      else if !(1 ≤ destination ∧ destination ≤ policy.maxRegisters) then
        .error (.registerOutOfBounds destination policy.maxRegisters)
      else .ok ()
  | .resultRow first count =>
      if !(count ≤ policy.maxResultWidth) then
        .error (.resultWidthExceeded count policy.maxResultWidth)
      else if !(count = 0 ∨ (1 ≤ first ∧ first + count - 1 ≤ policy.maxRegisters)) then
        .error (.registerOutOfBounds (if first = 0 then 0 else first + count - 1) policy.maxRegisters)
      else .ok ()
  | .seekRowid cursor missingTarget keyRegister =>
      if !(cursor < policy.maxCursors) then
        .error (.cursorOutOfBounds cursor policy.maxCursors)
      else if !(missingTarget = 0 ∨ missingTarget < codeSize) then
        .error (.branchTargetOutOfBounds missingTarget codeSize)
      else if !(1 ≤ keyRegister ∧ keyRegister ≤ policy.maxRegisters) then
        .error (.registerOutOfBounds keyRegister policy.maxRegisters)
      else .ok ()

/-- Whole-program well-formedness under `policy`: every fetched instruction
satisfies `InstructionWf policy program.size`. -/
def WellFormed (policy : Policy) (program : Program) : Prop :=
  ∀ (i : Nat) (instr : Instruction), program[i]? = some instr → InstructionWf policy program.size instr

/-- Validate and lower one untrusted raw VDBE instruction under `policy`. -/
def admitInstruction (policy : Policy) (codeSize : Nat) (raw : RawInstruction) :
    Except RejectionReason Instruction :=
  match raw.opcode.name? with
  | some name =>
      if name ∈ deniedOpcodeNames then .error (.deniedOpcode name)
      else match Vdbe.decode? raw with
        | none => .error (.unsupportedOpcode raw)
        | some instr => do
            checkInstruction policy codeSize instr
            return instr
  | none => .error (.unsupportedOpcode raw)

/-- Validate and lower an arbitrary untrusted `RawProgram` under `policy`. -/
def admitProgram (policy : Policy) (raw : Vdbe.RawProgram) : Except RejectionReason Program :=
  (raw.toList.mapM (admitInstruction policy raw.size)).map List.toArray

/-- Per-state isolation and resource-confinement invariant for a VM state
relative to `policy` and `host`. -/
structure StateInv (policy : Policy) (host : HostState) (s : State) : Prop where
  /-- Every non-null register lies within `[1, policy.maxRegisters]`. -/
  registersConfined : ∀ r, s.registers r ≠ .null → 1 ≤ r ∧ r ≤ policy.maxRegisters
  /-- Every open cursor has an in-bounds identifier and provenance from an
  authorized `(database, root)` entry in `host.databases`. -/
  cursorsConfined : ∀ cid cursor, s.cursors cid = some cursor →
    cid < policy.maxCursors ∧
    ∃ db root, policy.canRead db root = true ∧ host.databases db root = some cursor.table
  /-- Every emitted row respects the policy's result width bound. -/
  rowsBounded : ∀ row ∈ s.rows, row.length ≤ policy.maxResultWidth

/-- Host effects emitted by one VM step on `host.databases`.
Matches `VirtualMachine.Traced.stepWithTrace` for read and row events while
embedding into `Effect`. -/
def stepEffects (program : Program) (s : State) (outcome : Except Fault State) : List Effect :=
  if s.halted.isSome then [] else
    match program[s.pc]?, outcome with
    | some (.openRead _ root database), .ok _ => [.readTable database root true]
    | some (.openRead _ root database), .error _ => [.readTable database root false]
    | some (.resultRow first count), .ok _ =>
        [.emitRow ((List.range count).map fun offset => s.registers (first + offset))]
    | _, _ => []

/-- One isolated VM step returning emitted host effects and either the next
`(HostState, State)` or a VM fault. -/
def stepIsolated (host : HostState) (program : Program) (s : State) :
    List Effect × Except Fault (HostState × State) :=
  let next := step host.databases program s
  (stepEffects program s next, next.map fun after => (host, after))

/-- Result of a finite-prefix isolated VM execution. -/
structure RunOutcome where
  events : List Effect
  host : HostState
  result : RunResult

/-- Finite-prefix isolated VM execution up to `fuel` steps. -/
def runIsolated (host : HostState) (program : Program) : Nat → State → RunOutcome
  | fuel, s =>
      if s.halted.isSome then ⟨[], host, .halted s⟩ else
        match fuel with
        | 0 => ⟨[], host, .exhausted s⟩
        | fuel + 1 =>
          let (events, next) := stepIsolated host program s
          match next with
          | .error fault => ⟨events, host, .fault fault s⟩
          | .ok (host', after) =>
            let rest := runIsolated host' program fuel after
            ⟨events ++ rest.events, rest.host, rest.result⟩

/-- Outcome of validating and (if admitted) running an untrusted raw program. -/
inductive AdmittedOutcome where
  | rejected (reason : RejectionReason)
  | executed (outcome : RunOutcome)

/-- End-to-end admission gate followed by finite-prefix isolated execution
for an arbitrary untrusted `Vdbe.RawProgram`. -/
def admitAndRun (policy : Policy) (host : HostState) (raw : Vdbe.RawProgram)
    (fuel : Nat) : AdmittedOutcome :=
  match admitProgram policy raw with
  | .error reason => .rejected reason
  | .ok program => .executed (runIsolated host program fuel initial)

/-- Potential host effect of an unvalidated raw instruction, used to witness
disallowed effects in the absence of the admission gate. -/
def rawPotentialEffect (raw : RawInstruction) : Option Effect :=
  match raw.opcode.name? with
  | some "OpenWrite" | some "Insert" | some "InsertInt" | some "Delete" =>
      some (.writeTable raw.p3.toNat raw.p2.toNat)
  | some "Attach" =>
      some (.attachDb (match raw.p4 with | .text s => s | _ => ""))
  | some "LoadExtension" =>
      some (.loadExtension (match raw.p4 with | .text s => s | _ => ""))
  | some name =>
      if name ∈ deniedOpcodeNames then some (.hostEscape name) else none
  | none => some (.hostEscape "<numeric>")

end Silmaril.Machine.SQLite.VirtualMachine.Isolation
