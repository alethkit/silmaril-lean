module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
public import Silmaril.X86.Concurrency.Sqlite.Release.Thms
import Silmaril.X86.MemEvent.Thms
import Silmaril.X86.MemoryModel.Tso.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockStep

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.X86
open Silmaril.X86.Ext
open Silmaril.X86.MemoryModel.Tso
open Silmaril.X86.Concurrency.Sqlite.Release
open Silmaril.Process (Memory)

/-- Execution of the decoded instruction given the exact dword reads and
writes. The caller must still justify fetching the instruction at this point. -/
private theorem execExchange (s : State) (before after : Memory)
    (zero : s.read .rax = 0) (old : loadN before (s.read .rdi) 4 = some 1)
    (write : storeN before (s.read .rdi) 4 0 = some after) :
    Atomic9.exec exchange s before 2 =
      .ok {s.write .rax 1 with rip := s.rip + 2} after := by
  simp [exchange, Atomic9.exec, Atomic9.execNew, Atomic9.xchgStep, readRM,
    writeRM, Mem.ofReg, Mem.addr, Sz.bytes, Sz.read, Sz.write, zero, old, retire]
  rw [show storeN before (s.read .rdi) 4 0#64 = some after from write]
  rfl

private theorem readBacking_eq_readMem (bytes : Silmaril.Process.ByteMemory) (start length : Nat) :
    Memory.readBacking bytes start length = readMem (fun addr => bytes.get? addr) start length := by
  induction length generalizing start with
  | zero => rfl
  | succ length ih =>
    simp only [Memory.readBacking, readMem, ih]
    cases bytes.get? start <;> cases readMem (fun addr => bytes.get? addr) (start + 1) length <;> rfl

private theorem writeBytes_matches {before after : Memory} {lock : Nat}
    (h : before.writeBytes lock [0, 0, 0, 0] = some after) (addr : Nat) :
    after.bytes.get? addr = writeMem (fun a => before.bytes.get? a) lock [0, 0, 0, 0] addr := by
  by_cases inside : lock ≤ addr ∧ addr < lock + 4
  · have offset : addr - lock < 4 := by omega
    have shifted := Memory.writeBytes_get h (addr - lock) (by exact offset)
    rw [show lock + (addr - lock) = addr by omega] at shifted
    rw [shifted]
    have bound : addr - lock < ([0#8, 0#8, 0#8, 0#8] : List (BitVec 8)).length := offset
    simp [writeMem, entryByte, inside.1, List.getElem?_eq_getElem bound]
  · have outside : addr < lock ∨ lock + 4 ≤ addr := by omega
    have framed := Memory.writeBytes_writesOnly h
    rw [framed.2 addr outside]
    have empty : entryByte lock [0#8, 0#8, 0#8, 0#8] addr = none := by
      unfold entryByte
      split
      · apply List.getElem?_eq_none
        simp
        omega
      · rfl
    simp [writeMem, empty]

/-- The decoded exchange matches the actual central step of a FIFO release
under the supplied memory view, permissions, and flush witnesses. -/
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
        PeerBuffersAvoid start tid addr → finish.memory addr = viewMem start tid addr := by
  have byteView : (fun addr => before.bytes.get? addr) = issued.memory := funext backing
  have loaded : before.readBytes (s.read .rdi).toNat 4 = some [1, 0, 0, 0] := by
    unfold Memory.readBytes Memory.readWith
    change before.checkSpan .read (s.read .rdi).toNat 4 = true at readPerm
    rw [ite_eq_left readPerm, readBacking_eq_readMem, byteView]
    exact old
  have load : loadN before (s.read .rdi) 4 = some 1 := by simp [loadN, loaded]; rfl
  let after := {before with bytes := Memory.install before.bytes (s.read .rdi).toNat [0, 0, 0, 0]}
  have written : before.writeBytes (s.read .rdi).toNat [0, 0, 0, 0] = some after := by
    unfold Memory.writeBytes
    change before.checkSpan .write (s.read .rdi).toNat ([0, 0, 0, 0] : List (BitVec 8)).length = true at writePerm
    rw [ite_eq_left writePerm]
  have stored : storeN before (s.read .rdi) 4 0 = some after := written
  have weak : XWeakStep start ((.rmw tid (s.read .rdi).toNat [1, 0, 0, 0] [0, 0, 0, 0])) finish :=
    ⟨_, _, leadingFlushes, .rmw _ _ _ _ _ empty old rfl, trailingFlushes⟩
  refine ⟨after, ?_, Memory.writeBytes_writesOnly written, ?_, ?_,
    dword_release confined weak⟩
  · rw [MemEvent.atomic9_step_eq]
    change (MemEvent.atomic9Fetch before s.rip.toNat).bind _ = _
    rw [fetch]
    simp only [Option.bind_some, execExchange s before after zero load stored]
    rfl
  · simp [MemEvent.Event.singleCopy, aligned]
  · intro addr
    rw [← byteView]
    exact writeBytes_matches written addr

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockStep
