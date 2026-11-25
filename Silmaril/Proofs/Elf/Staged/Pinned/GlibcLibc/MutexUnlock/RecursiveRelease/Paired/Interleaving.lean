module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Defs
public import Silmaril.Machine.Execution
public import Silmaril.X86.Concurrency.Sqlite.Release.Defs
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired.Thms
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Confined.Thms
import Silmaril.X86.Concurrency.Sqlite.Release.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired.Interleaving

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.Machine.Execution (run)
open Silmaril.X86
open Silmaril.X86.Concurrency.Sqlite.Release
open Silmaril.X86.MemoryModel
open Silmaril.X86.MemoryModel.Tso hiding Execution

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
        sc.memory.bytes.get? address = finalFifo.memory address := by
  let base := (initial.core.read .rdi).toNat
  let initialBacking : Tso.Mem := fun address => initial.memory.bytes.get? address
  let selected := FifoData.dataEvents tid base users kind
  let reference : XState Nat := xembed initialBacking
  obtain ⟨sc, referenceFinal, exec, referencePath, _, _, compared⟩ :=
    RecursiveRelease.Paired.paired_final_bytes reference tid rfl rfl entry aligned lock writable
  refine ⟨sc, exec, ?_⟩
  intro address same initiallyConfined issuedConfined
  have safe : PeerBuffersAvoid reference tid address := by
    intro _ _ _ pending
    cases pending
  have referenceByte : referenceFinal.memory address =
      selected.foldl (fun byte e => byteEffect e address byte) (initialBacking address) :=
    (FifoData.Confined.release_byte referencePath safe).2
  have last : (events.filter (fun event => event.thread == tid)).getLast? =
      some (.rmw tid base [1, 0, 0, 0] FifoData.zeroDword) := by
    rw [issuer]
    rfl
  have fifoByte := (interleaving_last_rmw_backing path initiallyConfined issuedConfined last).2
  rw [issuer, same] at fifoByte
  exact (compared address).trans (referenceByte.trans fifoByte.symm)

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Paired.Interleaving
