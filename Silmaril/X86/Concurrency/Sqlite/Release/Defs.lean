module

public import Silmaril.X86.Concurrency.Sqlite.Defs

/-! # A SQLite-motivated lock release in the byte memory model

The primitive supplies a locked RMW event to the existing SC and FIFO TSO
models. This describes a release phase of the file-control model. It leaves
the linkage from a compiled mutex handler to the event as a separate task.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Sqlite.Release

open Silmaril.Machine.SqliteControl
open Silmaril.X86.MemoryModel.Tso

/-- No thread initially has a pending write covering the lock byte. -/
def BuffersAvoid (s : XState Nat) (lock : Nat) : Prop :=
  ∀ tid entry, entry ∈ s.buffer tid → entryByte entry.1 entry.2 lock = none

/-- Peers have no pending write covering the protected byte. The owner may have one. -/
def PeerBuffersAvoid (s : XState Nat) (owner addr : Nat) : Prop :=
  ∀ tid, tid ≠ owner → ∀ entry, entry ∈ s.buffer tid → entryByte entry.1 entry.2 addr = none

/-- A model primitive: one locked read of 1 and write of 0 at the lock byte. -/
def releaseEvent (tid lock : Nat) : XEvent Nat := .rmw tid lock [1] [0]

/-- One owner in the SQLite file-control release phase, with all peers idle. -/
def releaseInput (tid : Nat) (busy rc : Int32) : Config Phase :=
  ⟨⟨some tid, busy⟩, fun other => if other = tid then .release rc else .idle⟩

def IsRelease (tid lock : Nat) (_ : XState Nat) (run : Sqlite.Execution .fifo) : Prop :=
  run.labels = [releaseEvent tid lock]

def releasedView (tid lock : Nat) (busy : Int32) (m : Silmaril.X86.MemoryModel.Tso.Mem) : Shared :=
  ⟨if m lock = some 0 then none else some tid, busy⟩

/-- Observe the lock word after the whole weak step, including its trailing flushes. -/
def releaseProjection (tid lock : Nat) (busy : Int32) :
    Projection .control (XEvent Nat) (XState Nat) where
  event := fun e => if e = releaseEvent tid lock then some (.released tid) else none
  final := fun s => releasedView tid lock busy s.memory

/-- The lock byte initially represents an owned lock and is outside all pending writes. -/
def confined (tid lock : Nat) (busy rc : Int32) : Proposal (XState Nat) .control :=
  { pair | BuffersAvoid pair.1 lock ∧ pair.1.memory lock = some 1 ∧
    pair.2 = releaseInput tid busy rc }

/-- The issued primitive itself accesses only the lock byte. -/
def releaseFootprint (lock : Nat) : XState Nat → Config Phase → Set Nat := fun _ _ => {lock}

end Silmaril.X86.Concurrency.Sqlite.Release
