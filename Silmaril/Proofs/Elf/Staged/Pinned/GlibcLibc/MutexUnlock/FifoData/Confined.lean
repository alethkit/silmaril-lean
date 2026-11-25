module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Defs
public import Silmaril.X86.Concurrency.Sqlite.Release.Defs
import Silmaril.X86.Concurrency.Sqlite.Release.Thms
import Silmaril.X86.MemoryModel.Tso.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Confined

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.X86.MemoryModel.Tso hiding Execution
open Silmaril.X86.MemoryModel
open Silmaril.X86.Concurrency.Sqlite.Release (PeerBuffersAvoid owner_trace_view)

private theorem last_edge {initial final : XState Nat} {earlier : List (XEvent Nat)}
    {event : XEvent Nat} (trace : Tso.Execution XWeakStep initial (earlier ++ [event]) final) :
    ∃ before, XWeakStep before event final := by
  induction earlier generalizing initial with
  | nil => cases trace with
    | cons edge tail => cases tail; exact ⟨_, edge⟩
  | cons first rest ih => cases trace with
    | cons _ tail => exact ih tail

theorem release_byte {initial final : XState Nat} {tid base address : Nat}
    {users kind : BitVec 32}
    (path : Tso.Execution XWeakStep initial (FifoData.dataEvents tid base users kind) final)
    (safe : PeerBuffersAvoid initial tid address) :
    final.buffer tid = [] ∧
      final.memory address = writeMem (FifoData.committedStores (viewMem initial tid) base users)
        base FifoData.zeroDword address := by
  have actors : ∀ event ∈ FifoData.dataEvents tid base users kind, event.thread = tid := by
    intro event member
    simp only [FifoData.dataEvents, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have drained : final.buffer tid = [] := by
    change Tso.Execution XWeakStep initial
      ((FifoData.dataEvents tid base users kind).take 7 ++
        [.rmw tid base [1, 0, 0, 0] FifoData.zeroDword]) final at path
    obtain ⟨_, exchange⟩ := last_edge path
    exact weak_rmw_empty exchange
  have view := (owner_trace_view path actors safe).1
  have shared : viewMem final tid address = final.memory address := by
    simp [viewMem, drained, readBufByte]
  refine ⟨drained, ?_⟩
  rw [← shared, view]
  rfl

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Confined
