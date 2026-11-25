module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Thms
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Thms
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockPaired

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired

open Silmaril.X86
open Silmaril.X86.MemoryModel.Tso
open Silmaril.Machine.Execution (run)

/-- The eleven-step SC release and the selected eight-event FIFO schedule
agree on every backing byte. The FIFO issuer starts and ends drained, and
other threads' pending buffers remain the same during this schedule.
This compares endpoints of two finite executions. -/
theorem paired_final_bytes {initial : MState} {kind users : BitVec 32}
    (initialFifo : XState Nat) (tid : Nat)
    (same : initialFifo.memory = fun address => initial.memory.bytes.get? address)
    (issuerEmpty : initialFifo.buffer tid = [])
    (entry : RecursiveRelease.Entry initial kind users)
    (aligned : (initial.core.read .rdi).toNat % 4 = 0)
    (lock : initial.memory.readBytes (initial.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : initial.memory.Permitted .write (initial.core.read .rdi).toNat 4) :
    ∃ sc fifo,
      run Atomic9.step 11 initial = some sc ∧
      Silmaril.X86.MemoryModel.Tso.Execution XWeakStep initialFifo
        (FifoData.dataEvents tid (initial.core.read .rdi).toNat users kind) fifo ∧
      fifo.buffer tid = [] ∧
      (∀ peer, peer ≠ tid → fifo.buffer peer = initialFifo.buffer peer) ∧
      ∀ address, sc.memory.bytes.get? address = fifo.memory address :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockPaired.paired_final_bytes
    initialFifo tid same issuerEmpty entry aligned lock writable

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired
