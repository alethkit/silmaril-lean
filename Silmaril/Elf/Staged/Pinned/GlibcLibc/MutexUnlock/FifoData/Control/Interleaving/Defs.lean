module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Defs

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.X86.Concurrency.Sqlite
open Silmaril.X86.Concurrency.Sqlite.Release
open Silmaril.X86.MemoryModel.Tso hiding Execution
open Silmaril.X86.MemoryModel

/-- Select the eight issuer labels in order. Every issued peer access must fit
its allowance, and every issued peer write must avoid the four lock bytes. -/
def admitted (tid base : Nat) (users kind : BitVec 32) (peerBytes : Set Nat)
    (_ : XState Nat) (run : Silmaril.X86.Concurrency.Sqlite.Execution .fifo) : Prop :=
  run.labels.filter (fun event => event.thread == tid) = FifoData.dataEvents tid base users kind ∧
  ∀ event ∈ run.labels, event.thread ≠ tid →
    accessBytes event ⊆ peerBytes ∧
    ∀ address, base ≤ address → address < base + 4 → byteEffect event address none = none

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving
