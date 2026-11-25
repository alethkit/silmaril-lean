module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
public import Silmaril.X86.Concurrency.Sqlite.Release.Thms
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockStep

/-! One loaded instruction at an already reached exchange point.
Runtime installation of the SQLite callback, loader binding, and reachability
of the exchange from a recursive unlock are separate obligations. -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock

open Silmaril.X86
open Silmaril.X86.Ext
open Silmaril.X86.MemoryModel.Tso
open Silmaril.X86.Concurrency.Sqlite.Release
open Silmaril.Process (Memory)

/-- The decoded exchange matches the actual central step of a FIFO release
under an actual fetch, explicit byte view, permissions, and flush witnesses. -/
theorem step_and_publication
    (s : State) (before : Memory) (start issued finish : XState Nat) (tid : Nat)
    (fetch : MemEvent.atomic9Fetch before s.rip.toNat = some (exchange, 2))
    (zero : s.read .rax = 0)
    (aligned : (s.read .rdi).toNat % 4 = 0)
    (backing : ∀ addr, before.bytes.get? addr = issued.memory addr)
    (readPerm : before.Permitted .read (s.read .rdi).toNat 4)
    (writePerm : before.Permitted .write (s.read .rdi).toNat 4)
    (leadingFlushes : XFlushes start issued) (empty : issued.buffer tid = [])
    (old : readMem issued.memory (s.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (trailingFlushes : XFlushes {issued with memory := writeMem issued.memory (s.read .rdi).toNat [0, 0, 0, 0]} finish)
    (confined : ∀ addr, (s.read .rdi).toNat ≤ addr → addr < (s.read .rdi).toNat + 4 →
      BuffersAvoid start addr) :
    ∃ after : Memory, Atomic9.step ⟨s, before⟩ =
        some ⟨{s.write .rax 1 with rip := s.rip + 2}, after⟩ ∧
      Memory.WritesOnly before after (s.read .rdi).toNat 4 ∧
      MemEvent.Event.singleCopy ⟨.rmw, (s.read .rdi).toNat, 4, true⟩ = true ∧
      (∀ addr, after.bytes.get? addr = writeMem issued.memory (s.read .rdi).toNat [0, 0, 0, 0] addr) ∧
      (∀ addr, (s.read .rdi).toNat ≤ addr → addr < (s.read .rdi).toNat + 4 →
        finish.memory addr = some 0) ∧
      finish.buffer tid = [] ∧
      ∀ addr, (addr < (s.read .rdi).toNat ∨ (s.read .rdi).toNat + 4 ≤ addr) →
        PeerBuffersAvoid start tid addr → finish.memory addr = viewMem start tid addr :=
  Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockStep.step_and_publication s before start issued finish tid fetch zero aligned backing readPerm writePerm
    leadingFlushes empty old trailingFlushes confined

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
