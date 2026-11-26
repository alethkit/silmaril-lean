module

public import Silmaril.Machine.SQLite.VirtualMachine.Isolation.Defs
import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Isolation

/-! Public isolation theorems for the high-level read-only SQLite VDBE VM.

These theorems cover arbitrary admitted programs (via `WellFormed` or
`admitProgram`) over arbitrary `HostState` snapshots and arbitrary finite step
prefixes `fuel : Nat`:
- Static admission soundness (`admitProgram_wellFormed`): every admitted raw
  program is `WellFormed` under `policy`.
- Per-step isolation (`stepIsolated_isolation`): every step of a well-formed
  program from a `StateInv` state emits only `Effect.Allowed` host effects,
  leaves `HostState` unchanged, preserves `StateInv`, and agrees with
  `VirtualMachine.step`.
- Finite-prefix isolation (`runIsolated_isolation`): lifts per-step isolation
  to any finite `fuel : Nat` run prefix, whether halting, exhausting fuel, or
  faulting safely on malformed/runtime errors.
- End-to-end untrusted raw-program isolation (`admitAndRun_isolation` and
  `admitAndRun_no_denied_effects`): any untrusted `Vdbe.RawProgram` is either
  safely rejected prior to execution or executes with only policy-allowed
  effects, unchanged `HostState`, and preserved `StateInv`.

Explicit limits: these theorems do NOT establish confidentiality, termination,
blanket step/memory resource caps, SQL compiler postconditions, or C/ELF
refinement of `libsqlite3.so`.
-/

public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Isolation

open Silmaril.Formats.Sqlite

theorem effect_isAllowed_iff (policy : Policy) (e : Effect) :
    e.isAllowed policy = true ↔ e.Allowed policy :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.effect_isAllowed_iff policy e

theorem not_allowed_writeTable (policy : Policy) (db root : Nat) :
    ¬ (Effect.writeTable db root).Allowed policy :=
  id

theorem not_allowed_attachDb (policy : Policy) (name : String) :
    ¬ (Effect.attachDb name).Allowed policy :=
  id

theorem not_allowed_loadExtension (policy : Policy) (path : String) :
    ¬ (Effect.loadExtension path).Allowed policy :=
  id

theorem not_allowed_hostEscape (policy : Policy) (op : String) :
    ¬ (Effect.hostEscape op).Allowed policy :=
  id

theorem checkInstruction_ok_iff (policy : Policy) (codeSize : Nat) (instr : Instruction) :
    checkInstruction policy codeSize instr = .ok () ↔ InstructionWf policy codeSize instr :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.checkInstruction_ok_iff policy codeSize instr

theorem admitInstruction_wf {policy : Policy} {codeSize : Nat} {raw : RawInstruction}
    {instr : Instruction} (h : admitInstruction policy codeSize raw = .ok instr) :
    InstructionWf policy codeSize instr :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.admitInstruction_wf h

theorem admitProgram_wellFormed {policy : Policy} {raw : Vdbe.RawProgram} {program : Program}
    (h : admitProgram policy raw = .ok program) :
    WellFormed policy program :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.admitProgram_wellFormed h

theorem stateInv_initial (policy : Policy) (host : HostState) :
    StateInv policy host initial :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.stateInv_initial policy host

theorem execute_preserves_stateInv {policy : Policy} {codeSize : Nat} {host : HostState}
    {instr : Instruction} {s s' : State}
    (hwf : InstructionWf policy codeSize instr)
    (hinv : StateInv policy host s)
    (hexec : Vdbe.execute host.databases instr s = .ok s') :
    StateInv policy host s' :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.execute_preserves_stateInv hwf hinv hexec

theorem stepEffects_allowed {policy : Policy} {program : Program}
    (hwf : WellFormed policy program) (s : State) (outcome : Except Fault State) :
    ∀ e ∈ stepEffects program s outcome, e.Allowed policy :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.stepEffects_allowed hwf s outcome

/-- Per-step isolation for any well-formed program and invariant state. -/
theorem stepIsolated_isolation {policy : Policy} {host : HostState} {program : Program}
    {s : State} (hwf : WellFormed policy program) (hinv : StateInv policy host s) :
    (∀ e ∈ (stepIsolated host program s).1, e.Allowed policy) ∧
    (∀ host' s', (stepIsolated host program s).2 = .ok (host', s') →
      host' = host ∧ StateInv policy host' s' ∧ step host.databases program s = .ok s') ∧
    (∀ err, (stepIsolated host program s).2 = .error err →
      step host.databases program s = .error err) :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.stepIsolated_isolation hwf hinv

theorem runIsolated_result (host : HostState) (program : Program) (fuel : Nat) (s : State) :
    (runIsolated host program fuel s).result = run host.databases program fuel s :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.runIsolated_result host program fuel s

theorem runIsolated_host_unchanged (host : HostState) (program : Program) (fuel : Nat) (s : State) :
    (runIsolated host program fuel s).host = host :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.runIsolated_host_unchanged host program fuel s

/-- Finite-prefix isolation lifted to arbitrary `fuel : Nat` runs of any
well-formed program from any invariant state. -/
theorem runIsolated_isolation {policy : Policy} {host : HostState} {program : Program}
    (hwf : WellFormed policy program) (fuel : Nat) {s : State}
    (hinv : StateInv policy host s) :
    (∀ e ∈ (runIsolated host program fuel s).events, e.Allowed policy) ∧
    (runIsolated host program fuel s).host = host ∧
    StateInv policy (runIsolated host program fuel s).host (runIsolated host program fuel s).result.state ∧
    (runIsolated host program fuel s).result = run host.databases program fuel s :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.runIsolated_isolation hwf fuel hinv

/-- End-to-end isolation for any untrusted raw VDBE program: either safely
rejected before execution, or executed with only policy-allowed effects,
unchanged `HostState`, and preserved `StateInv`. -/
theorem admitAndRun_isolation (policy : Policy) (host : HostState)
    (raw : Vdbe.RawProgram) (fuel : Nat) :
    match admitAndRun policy host raw fuel with
    | .rejected _ => True
    | .executed out =>
        (∀ e ∈ out.events, e.Allowed policy) ∧
        out.host = host ∧
        StateInv policy out.host out.result.state ∧
        ∃ program, admitProgram policy raw = .ok program ∧
          out.result = run host.databases program fuel initial :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.admitAndRun_isolation policy host raw fuel

/-- Explicit absence of write, attach, extension, and escape effects across any
admitted finite run prefix. -/
theorem admitAndRun_no_denied_effects {policy : Policy} {host : HostState}
    {raw : Vdbe.RawProgram} {fuel : Nat} {out : RunOutcome}
    (hexec : admitAndRun policy host raw fuel = .executed out) :
    ∀ e ∈ out.events,
      (∀ db root, e ≠ .writeTable db root) ∧
      (∀ name, e ≠ .attachDb name) ∧
      (∀ path, e ≠ .loadExtension path) ∧
      (∀ op, e ≠ .hostEscape op) ∧
      (∀ db root found, e = .readTable db root found → policy.canRead db root = true) ∧
      (∀ cells, e = .emitRow cells → cells.length ≤ policy.maxResultWidth) :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.admitAndRun_no_denied_effects hexec

end Silmaril.Machine.SQLite.VirtualMachine.Isolation
