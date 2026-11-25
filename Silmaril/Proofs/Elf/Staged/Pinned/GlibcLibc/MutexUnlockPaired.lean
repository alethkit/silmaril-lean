module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Thms
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Thms
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.MemoryBytes

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockPaired

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.MemoryBytes (bytes_of_load readBacking_eq_fifoRead)
open Silmaril.X86
open Silmaril.X86.Ext (leBytes length_leBytes)
open Silmaril.X86.MemoryModel.Tso
open Silmaril.Machine.Execution (run)
open Silmaril.Process (Memory)

private theorem write_outside (memory : Silmaril.X86.MemoryModel.Tso.Mem)
    (start : Nat) (bytes : List Silmaril.X86.Byte) (address : Nat)
    (apart : address < start ∨ start + bytes.length ≤ address) :
    writeMem memory start bytes address = memory address := by
  have absent : entryByte start bytes address = none := by
    unfold entryByte
    split
    · exact List.getElem?_eq_none (by omega)
    · rfl
  rw [writeMem, absent]
  rfl

private theorem write_inside (memory : Silmaril.X86.MemoryModel.Tso.Mem)
    (start : Nat) (bytes : List Silmaril.X86.Byte) (address : Nat)
    (lo : start ≤ address) (hi : address < start + bytes.length) :
    writeMem memory start bytes address = bytes[address - start]? := by
  have within : address - start < bytes.length := by omega
  rw [writeMem, entryByte, ite_eq_left lo, List.getElem?_eq_getElem within]
  rfl

private theorem zero_inside (memory : Silmaril.X86.MemoryModel.Tso.Mem)
    (start address : Nat) (lo : start ≤ address) (hi : address < start + 4) :
    writeMem memory start FifoData.zeroDword address = some 0 := by
  rw [write_inside memory start FifoData.zeroDword address lo hi]
  have size : address - start < FifoData.zeroDword.length := by
    change address - start < 4
    omega
  rw [List.getElem?_eq_getElem size]
  have zero : FifoData.zeroDword[address - start] = 0 := by
    exact List.getElem_replicate (a := 0#8) (n := 4) (i := address - start) size
  rw [zero]

private theorem exact_backing {initial final : Memory} {base : Nat} {users : BitVec 32}
    (frame : initial.WritesOnly final base 16)
    (lock : ∀ address, base ≤ address → address < base + 4 → final.bytes.get? address = some 0)
    (fields : ∀ offset, offset < 4 →
      final.bytes.get? (base + 4 + offset) = some 0 ∧
      final.bytes.get? (base + 8 + offset) = some 0 ∧
      final.bytes.get? (base + 12 + offset) = (leBytes ((users - 1#32).setWidth 64) 4)[offset]?) :
    ∀ address, final.bytes.get? address =
      writeMem (FifoData.committedStores (fun location => initial.bytes.get? location) base users)
        base FifoData.zeroDword address := by
  intro address
  let memory : Silmaril.X86.MemoryModel.Tso.Mem := fun location => initial.bytes.get? location
  let d := writeMem memory (base + 4) FifoData.zeroDword
  let u := writeMem d (base + 12) (FifoData.usersDword users)
  let o := writeMem u (base + 8) FifoData.zeroDword
  have zeroSize : FifoData.zeroDword.length = 4 := rfl
  have usersSize : (FifoData.usersDword users).length = 4 := by simp [FifoData.usersDword]
  change final.bytes.get? address = writeMem o base FifoData.zeroDword address
  by_cases outside : address < base ∨ base + 16 ≤ address
  · rw [frame.2 address outside, write_outside o base FifoData.zeroDword address
      (by rw [zeroSize]; omega)]
    change memory address = writeMem u (base + 8) FifoData.zeroDword address
    rw [write_outside u (base + 8) FifoData.zeroDword address (by rw [zeroSize]; omega)]
    change memory address = writeMem d (base + 12) (FifoData.usersDword users) address
    rw [write_outside d (base + 12) (FifoData.usersDword users) address (by rw [usersSize]; omega)]
    change memory address = writeMem memory (base + 4) FifoData.zeroDword address
    rw [write_outside memory (base + 4) FifoData.zeroDword address (by rw [zeroSize]; omega)]
  · by_cases inLock : address < base + 4
    · rw [zero_inside o base address (by omega) inLock]
      exact lock address (by omega) inLock
    rw [write_outside o base FifoData.zeroDword address (by rw [zeroSize]; omega)]
    change final.bytes.get? address = writeMem u (base + 8) FifoData.zeroDword address
    by_cases inDepth : address < base + 8
    · rw [write_outside u (base + 8) FifoData.zeroDword address (.inl inDepth)]
      change final.bytes.get? address = writeMem d (base + 12) (FifoData.usersDword users) address
      rw [write_outside d (base + 12) (FifoData.usersDword users) address (.inl (by omega))]
      change final.bytes.get? address = writeMem memory (base + 4) FifoData.zeroDword address
      rw [zero_inside memory (base + 4) address (by omega) inDepth]
      have data := (fields (address - (base + 4)) (by omega)).1
      rwa [Nat.add_sub_of_le (by omega : base + 4 ≤ address)] at data
    by_cases inOwner : address < base + 12
    · rw [zero_inside u (base + 8) address (by omega) inOwner]
      have data := (fields (address - (base + 8)) (by omega)).2.1
      rwa [Nat.add_sub_of_le (by omega : base + 8 ≤ address)] at data
    · rw [write_outside u (base + 8) FifoData.zeroDword address (by rw [zeroSize]; omega)]
      change final.bytes.get? address = writeMem d (base + 12) (FifoData.usersDword users) address
      rw [write_inside d (base + 12) (FifoData.usersDword users) address
        (by omega) (by rw [usersSize]; omega)]
      have data := (fields (address - (base + 12)) (by omega)).2.2
      rwa [Nat.add_sub_of_le (by omega : base + 12 ≤ address)] at data

private theorem readMem_of_readBytes {memory : Memory} {address length : Nat}
    {bytes : List Silmaril.X86.Byte}
    (read : memory.readBytes address length = some bytes) :
    readMem (fun location => memory.bytes.get? location) address length = some bytes := by
  have permitted := Memory.readWith_permitted read
  unfold Memory.readBytes Memory.readWith at read
  rw [ite_eq_left (show memory.checkSpan .read address length = true from permitted),
    readBacking_eq_fifoRead] at read
  exact read

private theorem fifo_read_of_readBytes {memory : Memory} {address length : Nat}
    {bytes : List Silmaril.X86.Byte} {state : XState Nat} {tid : Nat}
    (same : state.memory = fun location => memory.bytes.get? location)
    (empty : state.buffer tid = [])
    (read : memory.readBytes address length = some bytes) :
    readView state tid address length = some bytes := by
  have view : viewMem state tid = state.memory := by
    funext location
    simp only [viewMem, empty, readBufByte, Option.none_or]
  unfold readView
  rw [view, same]
  exact readMem_of_readBytes read

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
      ∀ address, sc.memory.bytes.get? address = fifo.memory address := by
  let base := initial.core.read .rdi
  have nowrap : base.toNat + 20 ≤ 2 ^ 64 := entry.noWrap
  have address (offset : Nat) (small : offset < 20) :
      (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  have depth : readView initialFifo tid (base.toNat + 4) 4 = some [1, 0, 0, 0] := by
    have got := fifo_read_of_readBytes same issuerEmpty (bytes_of_load (by decide) entry.depthOne)
    rw [show (base + 4#64).toNat = base.toNat + 4 from address 4 (by decide)] at got
    exact got
  have usersRead : readView initialFifo tid (base.toNat + 12) 4 = some (leBytes (users.setWidth 64) 4) := by
    have got := fifo_read_of_readBytes same issuerEmpty (bytes_of_load (by decide) entry.usersRead)
    rw [show (base + 12#64).toNat = base.toNat + 12 from address 12 (by decide)] at got
    exact got
  have kindRead : readView initialFifo tid (base.toNat + 16) 4 = some (leBytes (kind.setWidth 64) 4) := by
    have got := fifo_read_of_readBytes same issuerEmpty (bytes_of_load (by decide) entry.kindRead)
    rw [show (base + 16#64).toNat = base.toNat + 16 from address 16 (by decide)] at got
    exact got
  have flag : readView initialFifo tid 0x20c040 1 = some [0] := by
    have got := fifo_read_of_readBytes same issuerEmpty
      (bytes_of_load (by decide) entry.threadRead)
    have flagAddr : (0x20c040#64).toNat = 0x20c040 := by decide +kernel
    have flagBytes : leBytes 0#64 1 = [0#8] := by decide +kernel
    change readView initialFifo tid (0x20c040#64).toNat 1 = some (leBytes 0#64 1) at got
    rw [flagAddr, flagBytes] at got
    exact got
  have old : readMem initialFifo.memory base.toNat 4 = some [1, 0, 0, 0] := by
    rw [same]
    exact readMem_of_readBytes lock
  obtain ⟨sc, scRun, _, _, frame, clear, fields⟩ :=
    RecursiveRelease.private_through_exchange_sc_fields entry aligned lock writable
  obtain ⟨fifo, fifoRun, empty, fifoBytes, peers⟩ :=
    FifoData.data_and_release initialFifo tid base.toNat users kind issuerEmpty
      depth usersRead kindRead flag (entry.threadApart.elim Or.inr Or.inl) old
  refine ⟨sc, fifo, scRun, fifoRun, empty, peers, ?_⟩
  rw [fifoBytes, same]
  exact exact_backing frame clear fields

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockPaired
