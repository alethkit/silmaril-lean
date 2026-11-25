module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Defs
public import Silmaril.X86.Concurrency.Sqlite.Release.Defs

/-! The abstract SQLite control release associated with the eight issued
data events of the selected glibc unlock path. The contract concerns FIFO
executions of those labels, including silent propagation. -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control

open Silmaril.X86.Concurrency.Sqlite
open Silmaril.X86.Concurrency.Sqlite.Release (BuffersAvoid releaseInput releasedView)
open Silmaril.X86.MemoryModel.Tso
open Silmaril.Machine.SqliteControl

/-- The only labelled event that emits the control release. -/
def exchange (tid base : Nat) : XEvent Nat :=
  .rmw tid base [1, 0, 0, 0] FifoData.zeroDword

/-- All issued data bytes, including the kind field and private-threading flag. -/
def footprint (base : Nat) : Set Nat :=
  {address | (base ≤ address ∧ address < base + 20) ∨ address = 0x20c040}

/-- The dword exchange emits a release. The endpoint observes the backing lock byte
after any trailing propagation; it carries the supplied abstract busy count. -/
def projection (tid base : Nat) (busy : Int32) :
    Projection .control (XEvent Nat) (XState Nat) where
  event
    | event@(.rmw ..) => if event = exchange tid base then some (.released tid) else none
    | _ => none
  final := fun state => releasedView tid base busy state.memory

/-- The backing lock is initially held, and pending stores avoid all four lock bytes. -/
def confined (tid base : Nat) (busy rc : Int32) : Proposal (XState Nat) .control :=
  {pair | (∀ address, base ≤ address → address < base + 4 → BuffersAvoid pair.1 address) ∧
    readMem pair.1.memory base 4 = some [1, 0, 0, 0] ∧ pair.2 = releaseInput tid busy rc}

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control
