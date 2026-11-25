module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs
public import Silmaril.Process.Mt.X86.Defs
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.X86.Str9FsXN.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ProcessStep

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.Process (Memory)
open Silmaril.Process.Mt (MtCfg MtStep PrimTable Base TRec TsoS setTh tso)
open Silmaril.X86
open Silmaril.X86.Ext

private def listedExchange : Str9FsXN.Instr :=
  .base (.base (.new (.atomic (.xchg .d (.mem (Mem.ofReg .rdi none 0)) .rax))))

/-- The process's instruction branch executes the pinned dword exchange and
uses the configured access list. The mapped state is already at the opcode. -/
theorem exchange_dispatch {γ : Type} (env : Silmaril.Process.Mt.X86.Env γ) (tid : Nat)
    (ghost : γ) (core : Silmaril.Process.Mt.X86.Core) (before : Memory)
    (loaded : Loaded before core.core.rip exchangeBytes)
    (primitive : env.prims.find? (·.1 == core.core.rip) = none)
    (contract : env.libs.find? (·.1 == core.core.rip) = none)
    (zero : core.core.read .rax = 0)
    (old : before.readBytes (core.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : before.Permitted .write (core.core.read .rdi).toNat 4) :
    ∃ after,
      before.writeBytes (core.core.read .rdi).toNat [0, 0, 0, 0] = some after ∧
      Silmaril.Process.Mt.X86.step env tid core before ghost
        (.step ⟨{ core.core.write .rax 1 with rip := core.core.rip + 2 }, core.xmm⟩
          (env.acc core before) after) ∧
      before.WritesOnly after (core.core.read .rdi).toNat 4 := by
  let address := (core.core.read .rdi).toNat
  let after := { before with bytes := Memory.install before.bytes address [0, 0, 0, 0] }
  let next := { core.core.write .rax 1 with rip := core.core.rip + 2 }
  have written : before.writeBytes address [0, 0, 0, 0] = some after := by
    unfold Memory.writeBytes
    change before.checkSpan .write address ([0, 0, 0, 0] : List Byte).length = true at writable
    rw [ite_eq_left writable]
  have read : loadN before (core.core.read .rdi) 4 = some 1 := by
    simp [loadN, old]
    rfl
  have exec : Str9FsXN.exec listedExchange core.core before 2 = .ok next after := by
    change Atomic9.exec exchange core.core before 2 = .ok next after
    simp [exchange, Atomic9.exec, Atomic9.execNew, Atomic9.xchgStep, readRM,
      writeRM, Mem.ofReg, Mem.addr, Sz.bytes, Sz.read, Sz.write, zero, read, retire, next]
    rw [show storeN before (core.core.read .rdi) 4 0#64 = some after from written]
    rfl
  have actual : Str9FsXN.step ⟨⟨core.core, before⟩, core.xmm⟩ = some ⟨⟨next, after⟩, core.xmm⟩ :=
    Str9FsXN.step_of_listed (o := 0) (l := 2) loaded (by simp) (by decide) (by decide +kernel) exec
  have fetched : before.fetchBytes core.core.rip.toNat 2 = some exchangeBytes := loaded
  have noSyscall : before.fetchBytes core.core.rip.toNat 2 ≠ some Silmaril.Process.Mt.X86.syscallBytes := by
    rw [fetched]
    decide
  refine ⟨after, written, ?_, Memory.writeBytes_writesOnly written⟩
  simp [Silmaril.Process.Mt.X86.step, primitive, contract, noSyscall, actual, next]

/-- On a drained issuer view, a process environment supplying the decoded
locked access commits the successful exchange directly to shared backing. -/
theorem exchange_process_commit {γ : Type} (env : Silmaril.Process.Mt.X86.Env γ) (tid : Nat)
    (ghost : γ) (core : Silmaril.Process.Mt.X86.Core) (initial : Silmaril.Process.Mt.TsoS)
    (loaded : Loaded initial.mem core.core.rip exchangeBytes)
    (primitive : env.prims.find? (·.1 == core.core.rip) = none)
    (contract : env.libs.find? (·.1 == core.core.rip) = none)
    (zero : core.core.read .rax = 0)
    (old : initial.mem.readBytes (core.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : initial.mem.Permitted .write (core.core.read .rdi).toNat 4)
    (empty : initial.buf tid = [])
    (accesses : env.acc core initial.mem = some (MemEvent.atomic9Accesses exchange core.core 2)) :
    ∃ after : Memory,
      Silmaril.Process.Mt.X86.step env tid core (Silmaril.Process.Mt.tso.view initial tid) ghost
        (.step ⟨{ core.core.write .rax 1 with rip := core.core.rip + 2 }, core.xmm⟩
          (some (MemEvent.atomic9Accesses exchange core.core 2)) after) ∧
      Silmaril.Process.Mt.tso.user tid (some (MemEvent.atomic9Accesses exchange core.core 2))
        initial after { initial with mem := after } ∧
      initial.mem.writeBytes (core.core.read .rdi).toNat [0, 0, 0, 0] = some after ∧
      initial.mem.WritesOnly after (core.core.read .rdi).toNat 4 := by
  have shared : Silmaril.Process.Mt.tso.view initial tid = initial.mem :=
    Silmaril.Process.Mt.tso.view_synced empty
  obtain ⟨after, written, dispatched, frame⟩ := exchange_dispatch env tid ghost core initial.mem
    loaded primitive contract zero old writable
  rw [accesses] at dispatched
  refine ⟨after, ?_, ?_, written, frame⟩
  · rw [shared]
    exact dispatched
  · rw [access]
    exact ⟨frame.1, empty, rfl⟩

open Silmaril.Process.Mt.X86 (Env Core mtX MtProc)

/-- One actual process step of a running thread at the mapped exchange. The
process rule updates that thread and shared memory through its TSO commit. -/
theorem exchange_process_step {γ : Type} (env : Env γ) (primitives : PrimTable γ)
    (base : Base γ) (tid : Nat) (config : MtCfg Core γ TsoS) (thread : TRec Core) (core : Core)
    (live : config.Live (mtX env)) (selected : config.th tid = some thread)
    (running : thread.st = .run core)
    (loaded : Loaded config.ms.mem core.core.rip exchangeBytes)
    (primitive : env.prims.find? (·.1 == core.core.rip) = none)
    (contract : env.libs.find? (·.1 == core.core.rip) = none)
    (zero : core.core.read .rax = 0)
    (old : config.ms.mem.readBytes (core.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : config.ms.mem.Permitted .write (core.core.read .rdi).toNat 4)
    (empty : config.ms.buf tid = [])
    (accesses : env.acc core config.ms.mem = some (MemEvent.atomic9Accesses exchange core.core 2)) :
    ∃ after : Memory,
      let next : Core := ⟨{ core.core.write .rax 1 with rip := core.core.rip + 2 }, core.xmm⟩
      MtProc env tso primitives base config
        { config with
          th := setTh config.th tid { thread with st := .run next }
          ms := { config.ms with mem := after } } ∧
      config.ms.mem.writeBytes (core.core.read .rdi).toNat [0, 0, 0, 0] = some after ∧
      config.ms.mem.WritesOnly after (core.core.read .rdi).toNat 4 := by
  obtain ⟨after, step, commit, written, frame⟩ :=
    exchange_process_commit env tid config.g core config.ms loaded primitive contract
      zero old writable empty accesses
  exact ⟨after, MtStep.user live selected running step commit, written, frame⟩

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ProcessStep
