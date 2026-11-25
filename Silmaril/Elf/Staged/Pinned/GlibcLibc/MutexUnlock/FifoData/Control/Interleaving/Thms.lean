module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.X86.Concurrency.Sqlite
open Silmaril.X86.Concurrency.Sqlite.Release
open Silmaril.X86.MemoryModel.Tso hiding Execution
open Silmaril.X86.MemoryModel

/-- The selected exchange clears all four lock bytes and drains the issuer
through the endpoint. Initially pending and newly issued peer writes must
avoid the lock bytes, including writes issued after the exchange. -/
theorem released_lock {initial final : XState Nat} {events : List (XEvent Nat)}
    {tid base : Nat} {users kind : BitVec 32}
    (path : Tso.Execution XWeakStep initial events final)
    (issuer : events.filter (fun event => event.thread == tid) = FifoData.dataEvents tid base users kind)
    (initiallyConfined : ∀ address, base ≤ address → address < base + 4 →
      PeerBuffersAvoid initial tid address)
    (issuedConfined : ∀ event ∈ events, event.thread ≠ tid →
      ∀ address, base ≤ address → address < base + 4 → byteEffect event address none = none) :
    final.buffer tid = [] ∧ ∀ address, base ≤ address → address < base + 4 →
      final.memory address = some 0 :=
  Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving.released_lock path issuer initiallyConfined issuedConfined

/-- Every admitted FIFO interleaving from the existing confined input proposal
projects to one SQLite control release and fits the issuer and peer allowance
union. Erasing peer labels from the observation leaves their bytes counted. -/
theorem confined_sound (tid base : Nat) (busy rc : Int32)
    (users kind : BitVec 32) (peerBytes : Set Nat) :
    Sound .fifo id (admitted tid base users kind peerBytes)
      (FifoData.Control.projection tid base busy)
      (fun _ _ => FifoData.Control.footprint base ∪ peerBytes)
      (FifoData.Control.confined tid base busy rc) :=
  Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving.confined_sound tid base busy rc users kind peerBytes

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving
