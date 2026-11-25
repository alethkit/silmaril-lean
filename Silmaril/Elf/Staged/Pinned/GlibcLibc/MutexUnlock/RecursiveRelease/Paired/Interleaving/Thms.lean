module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Defs
public import Silmaril.Machine.Execution
public import Silmaril.X86.Concurrency.Sqlite.Release.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired.Interleaving

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired.Interleaving

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.Machine.Execution (run)
open Silmaril.X86
open Silmaril.X86.Concurrency.Sqlite.Release
open Silmaril.X86.MemoryModel
open Silmaril.X86.MemoryModel.Tso hiding Execution

/-- Compare the eleven-step Atomic9 endpoint with every modeled FIFO run of
the selected issuer labels, including runs with issued peer events. The
final backing byte agrees where the initial issuer view matches the SC
input and both initially pending and newly issued peer writes avoid the
byte. The execution comparison stops at the exchange. -/
theorem paired_backing_of_issuer_trace {initial : MState}
    {initialFifo finalFifo : XState Nat} {events : List (XEvent Nat)}
    {tid : Nat} {kind users : BitVec 32}
    (path : Tso.Execution XWeakStep initialFifo events finalFifo)
    (issuer : events.filter (fun event => event.thread == tid) =
      FifoData.dataEvents tid (initial.core.read .rdi).toNat users kind)
    (entry : RecursiveRelease.Entry initial kind users)
    (aligned : (initial.core.read .rdi).toNat % 4 = 0)
    (lock : initial.memory.readBytes (initial.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : initial.memory.Permitted .write (initial.core.read .rdi).toNat 4) :
    ∃ sc, run Atomic9.step 11 initial = some sc ∧
      ∀ address, viewMem initialFifo tid address = initial.memory.bytes.get? address →
        PeerBuffersAvoid initialFifo tid address →
        (∀ event ∈ events, event.thread ≠ tid → byteEffect event address none = none) →
        sc.memory.bytes.get? address = finalFifo.memory address :=
  Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired.Interleaving.paired_backing_of_issuer_trace path issuer entry aligned lock writable

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired.Interleaving
