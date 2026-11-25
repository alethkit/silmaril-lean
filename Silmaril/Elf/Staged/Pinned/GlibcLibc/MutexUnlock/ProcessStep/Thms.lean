module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs
public import Silmaril.Process.Mt.X86.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ProcessStep

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ProcessStep

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.Process (Memory)
open Silmaril.Process.Mt (MtCfg MtStep PrimTable Base TRec TsoS setTh tso)
open Silmaril.X86
open Silmaril.X86.Ext

open Silmaril.Process.Mt.X86 (Env Core mtX MtProc)

/-- The plain instruction dispatcher executes the mapped dword exchange and
carries the environment's access list. It writes four zero bytes at RDI and
keeps XMM state, other integer registers, flags and mapping regions. -/
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
      before.WritesOnly after (core.core.read .rdi).toNat 4 :=
  Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ProcessStep.exchange_dispatch env tid ghost core before loaded primitive contract zero old writable

/-- When the issuer is drained and the environment supplies the decoded
locked access, dispatch and the process TSO memory commit agree on the
same successor memory. -/
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
      initial.mem.WritesOnly after (core.core.read .rdi).toNat 4 :=
  Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ProcessStep.exchange_process_commit env tid ghost core initial loaded primitive contract zero old writable
    empty accesses

/-- The running thread at the mapped opcode takes one process step through
the configured locked access and the TSO commit. It advances RIP by two,
returns the old dword in RAX, and changes backing only within that dword. -/
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
      config.ms.mem.WritesOnly after (core.core.read .rdi).toNat 4 :=
  Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ProcessStep.exchange_process_step env primitives base tid config thread core live selected running loaded
    primitive contract zero old writable empty accesses

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ProcessStep
