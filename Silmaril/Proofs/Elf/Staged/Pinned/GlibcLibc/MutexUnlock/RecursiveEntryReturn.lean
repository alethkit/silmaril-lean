module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn.Defs
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue.Thms
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch.Thms
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck.Thms
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn
open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN leBytes)
open Silmaril.Machine.Execution (run run_add)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Process (Memory)

private theorem recursive_entry_owner {initial : MState} {threadId : BitVec 32}
    (rip : initial.core.rip = 0xa1b50)
    (entry : Loaded initial.memory 0xa1b50 RecursivePrologue.codeBytes)
    (dispatch : Loaded initial.memory 0xa1bd0 RecursiveDispatch.dispatchBytes)
    (recursive : Loaded initial.memory 0xa1be7 RecursiveDispatch.recursiveBytes)
    (ownerCode : Loaded initial.memory 0xa1bf2 OwnerCheck.ownerBytes)
    (kind : loadN initial.memory (initial.core.read .rdi + 16#64) 4 = some 1#64)
    (thread : loadN initial.memory (initial.core.fsBase + 0x2d0#64) 4 = some (threadId.setWidth 64))
    (owner : loadN initial.memory (initial.core.read .rdi + 8#64) 4 = some (threadId.setWidth 64))
    (writable : initial.memory.Permitted .write (savedSlot initial).toNat 8)
    (codeApart : SavedApart initial 0xa1b50 (0xa1c06 - 0xa1b50))
    (kindApart : SavedApart initial (initial.core.read .rdi + 16#64).toNat 4)
    (threadApart : SavedApart initial (initial.core.fsBase + 0x2d0#64).toNat 4)
    (ownerApart : SavedApart initial (initial.core.read .rdi + 8#64).toNat 4) :
    ∃ final, run Atomic9.step 20 initial = some final ∧ final.core.rip = 0xa1c06 ∧
      final.core.read .rax = threadId.setWidth 64 ∧ final.core.read .rdx = 1 ∧
      final.core.read .rbp = savedSlot initial ∧ final.core.read .rsp = savedSlot initial - 16#64 ∧
      (∀ reg, reg ≠ .rax → reg ≠ .rdx → reg ≠ .rbp → reg ≠ .rsp →
        final.core.read reg = initial.core.read reg) ∧ final.core.fsBase = initial.core.fsBase ∧
      initial.memory.writeBytes (savedSlot initial).toNat (encodeWords [initial.core.read .rbp]) =
        some final.memory ∧ initial.memory.WritesOnly final.memory (savedSlot initial).toNat 8 := by
  have spanApart {address size : Nat} (lo : 0xa1b50 ≤ address) (hi : address + size ≤ 0xa1c06) :
      SavedApart initial address size := by
    unfold SavedApart at codeApart ⊢
    omega
  have entryApart : (savedSlot initial).toNat + 8 ≤ 0xa1b50 ∨
      0xa1b6f ≤ (savedSlot initial).toNat :=
    (spanApart (address := 0xa1b50) (size := 31) (by decide) (by decide)).symm
  obtain ⟨prologue, first, pRip, _, pRdx, pRbp, pRsp, pRegs, pFs, written, framed⟩ :=
    RecursivePrologue.recursive_prologue rip entry kind writable entryApart
  have transferCode {address : Word} {bytes : List Byte}
      (loaded : Loaded initial.memory address bytes)
      (apart : SavedApart initial address.toNat bytes.length) :
      Loaded prologue.memory address bytes := by
    unfold Loaded Memory.fetchBytes at loaded ⊢
    rw [Silmaril.X86.Memory.readWith_writesOnly framed .execute _ _ apart]
    exact loaded
  have transferRead {address : Word} {size : Nat} {value : Word}
      (read : loadN initial.memory address size = some value)
      (apart : SavedApart initial address.toNat size) :
      loadN prologue.memory address size = some value := by
    unfold loadN Memory.readBytes at read ⊢
    rw [Silmaril.X86.Memory.readWith_writesOnly framed .read _ _ apart]
    exact read
  have pRdi : prologue.core.read .rdi = initial.core.read .rdi :=
    pRegs .rdi (by decide) (by decide) (by decide) (by decide)
  have pKind : loadN prologue.memory (prologue.core.read .rdi + 16#64) 4 = some 1#64 := by
    rw [pRdi]
    exact transferRead kind kindApart
  obtain ⟨dispatched, second, dRip, _, dRegs, dFs, dMemory⟩ :=
    RecursiveDispatch.recursive_dispatch pRip pRdx
      (transferCode dispatch (spanApart (by decide) (by decide)))
      (transferCode recursive (spanApart (by decide) (by decide))) pKind
  have dOwnerCode : Loaded dispatched.memory 0xa1bf2 OwnerCheck.ownerBytes := by
    rw [dMemory]
    exact transferCode ownerCode (spanApart (by decide) (by decide))
  have dThread : loadN dispatched.memory (dispatched.core.fsBase + 0x2d0#64) 4 =
      some (threadId.setWidth 64) := by
    rw [dMemory, dFs, pFs]
    exact transferRead thread threadApart
  have dOwner : loadN dispatched.memory (dispatched.core.read .rdi + 8#64) 4 =
      some (threadId.setWidth 64) := by
    rw [dMemory, dRegs .rdi (by decide), pRdi]
    exact transferRead owner ownerApart
  obtain ⟨final, third, endpoint, eax, oRegs, oFs, oMemory⟩ :=
    OwnerCheck.owner_check dRip dOwnerCode dThread dOwner
  have regFrame (reg : Reg) (ne : reg ≠ .rax) :
      final.core.read reg = prologue.core.read reg := (oRegs reg ne).trans (dRegs reg ne)
  refine ⟨final, ?_, ?_, eax, (regFrame .rdx (by decide)).trans pRdx,
    (regFrame .rbp (by decide)).trans pRbp, (regFrame .rsp (by decide)).trans pRsp,
    ?_, oFs.trans (dFs.trans pFs), ?_, ?_⟩
  · change run Atomic9.step (11 + (6 + 3)) initial = some final
    rw [run_add, first]
    change run Atomic9.step (6 + 3) prologue = some final
    rw [run_add, second]
    exact third
  · simpa only [ite_true] using endpoint
  · exact fun reg a d b s => (regFrame reg a).trans (pRegs reg a d s b)
  · rw [oMemory, dMemory]
    exact written
  · rw [oMemory, dMemory]
    exact framed

theorem recursive_entry_return {initial : MState} {threadId users : BitVec 32} {target : Word}
    (inputs : Entry initial threadId users target) :
    ∃ final, run Atomic9.step 37 initial = some final ∧ final.core.rip = target ∧
      final.core.read .rax = 0#64 ∧ final.core.read .rbp = initial.core.read .rbp ∧
      final.core.read .rsp = initial.core.read .rsp + 8#64 ∧
      initial.memory.WritesWithin final.memory (fun address =>
        ((savedSlot initial).toNat ≤ address ∧ address < (savedSlot initial).toNat + 8) ∨
        ((initial.core.read .rdi).toNat ≤ address ∧ address < (initial.core.read .rdi).toNat + 16)) ∧
      (∀ offset, offset < 8 → final.memory.bytes.get? ((savedSlot initial).toNat + offset) =
        (encodeWords [initial.core.read .rbp])[offset]?) ∧
      ∀ offset, offset < 4 →
        let base := (initial.core.read .rdi).toNat
        final.memory.bytes.get? (base + offset) = some 0 ∧
        final.memory.bytes.get? (base + 4 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 8 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 12 + offset) = (leBytes ((users - 1#32).setWidth 64) 4)[offset]? := by
  obtain ⟨rip, entry, dispatch, recursive, ownerCode, thread, owner, release, aligned, lock,
    lockWrite, compare, epilogue, savedWrite, savedRead, targetSlot, codeApart, mutexApart,
    threadApart, flagApart, savedTargetApart, targetMutexApart⟩ := inputs
  let base := initial.core.read .rdi
  let slot := (savedSlot initial).toNat
  have address (delta : Nat) (small : delta < 20) :
      (base + BitVec.ofNat 64 delta).toNat = base.toNat + delta := by
    have fit : base.toNat + 20 ≤ 2 ^ 64 := release.noWrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : delta < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  have mutexSpan (delta size : Nat) (small : delta < 20) (fits : delta + size ≤ 20) :
      SavedApart initial (base + BitVec.ofNat 64 delta).toNat size := by
    rw [address delta small]
    unfold SavedApart at mutexApart ⊢
    change base.toNat + 20 ≤ slot ∨ slot + 8 ≤ base.toNat at mutexApart
    change base.toNat + delta + size ≤ slot ∨ slot + 8 ≤ base.toNat + delta
    omega
  have codeSpan {address size : Nat} (lo : 0xa1b50 ≤ address) (hi : address + size ≤ 0xa1c10) :
      SavedApart initial address size := by
    unfold SavedApart at codeApart ⊢
    omega
  have kind : loadN initial.memory (base + 16#64) 4 = some 1#64 := release.kindRead
  obtain ⟨depth, entryRun, pc, _, _, rbp, _, regs, _, wrote, frame⟩ :=
    recursive_entry_owner rip entry dispatch recursive ownerCode kind thread owner savedWrite
      (codeSpan (by decide) (by decide)) (mutexSpan 16 4 (by decide) (by decide))
      threadApart (mutexSpan 8 4 (by decide) (by decide))
  have rdi : depth.core.read .rdi = base := regs .rdi (by decide) (by decide) (by decide) (by decide)
  have fetchFramed {start : Word} {bytes : List Byte} (loaded : Loaded initial.memory start bytes)
      (apart : SavedApart initial start.toNat bytes.length) :
      Loaded depth.memory start bytes := by
    unfold Loaded Memory.fetchBytes at loaded ⊢
    rw [Silmaril.X86.Memory.readWith_writesOnly frame .execute _ _ apart]
    exact loaded
  have readFramed {start : Word} {size : Nat} {value : Word} (read : loadN initial.memory start size = some value)
      (apart : SavedApart initial start.toNat size) : loadN depth.memory start size = some value := by
    unfold loadN Memory.readBytes at read ⊢
    rw [Silmaril.X86.Memory.readWith_writesOnly frame .read _ _ apart]
    exact read
  have permitted (access : Silmaril.Process.Access) (start size : Nat) :
      depth.memory.Permitted access start size ↔ initial.memory.Permitted access start size := by
    unfold Memory.Permitted
    rw [Silmaril.X86.Memory.checkSpan_congr frame.1]
  have reached : RecursiveRelease.Entry depth 1 users := by
    refine ⟨pc, fetchFramed release.depthCode (codeSpan (by decide) (by decide)),
      fetchFramed release.updateCode (codeSpan (by decide) (by decide)),
      fetchFramed release.selectCode (codeSpan (by decide) (by decide)),
      fetchFramed release.clearCode (codeSpan (by decide) (by decide)),
      fetchFramed release.exchangeCode (codeSpan (by decide) (by decide)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, release.privateKind,
      readFramed release.threadRead flagApart, ?_⟩
    · rw [rdi]; exact readFramed release.depthOne (mutexSpan 4 4 (by decide) (by decide))
    · rw [rdi]; exact readFramed release.usersRead (mutexSpan 12 4 (by decide) (by decide))
    · rw [rdi]; exact readFramed release.kindRead (mutexSpan 16 4 (by decide) (by decide))
    · rw [rdi]; exact (permitted _ _ _).2 release.depthWrite
    · rw [rdi]; exact (permitted _ _ _).2 release.ownerWrite
    · rw [rdi]; exact (permitted _ _ _).2 release.usersWrite
    · rw [rdi]; exact release.noWrap
    · rw [rdi]; exact release.codeApart
    · rw [rdi]; exact release.threadApart
  have atLock : depth.memory.readBytes (depth.core.read .rdi).toNat 4 = some [1, 0, 0, 0] := by
    rw [rdi, Memory.readBytes, Silmaril.X86.Memory.readWith_writesOnly frame .read _ _]
    · exact lock
    · have apart := mutexSpan 0 4 (by decide) (by decide)
      rw [BitVec.add_zero] at apart
      unfold SavedApart at apart
      exact apart
  have atWrite : depth.memory.Permitted .write (depth.core.read .rdi).toNat 4 := by
    rw [rdi]
    exact (permitted _ _ _).2 lockWrite
  have atAlign : (depth.core.read .rdi).toNat % 4 = 0 := by rw [rdi]; exact aligned
  have atSlot : depth.memory.readBytes (depth.core.read .rbp).toNat 8 =
      some (encodeWords [initial.core.read .rbp]) := by
    rw [rbp]
    have read := Memory.readWith_eq depth.memory .read slot (encodeWords [initial.core.read .rbp])
      (by rw [length_encodeWords_singleton]; exact (permitted _ _ _).2 savedRead)
      (Memory.writeBytes_get wrote)
    rwa [length_encodeWords_singleton] at read
  have targetAddress : depth.core.read .rbp + 8#64 = initial.core.read .rsp := by
    rw [rbp]
    simp [savedSlot]
  have atTarget : depth.memory.readBytes (depth.core.read .rbp + 8#64).toNat 8 =
      some (encodeWords [target]) := by
    rw [targetAddress, Memory.readBytes,
      Silmaril.X86.Memory.readWith_writesOnly frame .read _ _ savedTargetApart]
    exact targetSlot
  have slotVsMutex : RecursiveRelease.Return.StackSlotApart (depth.core.read .rdi).toNat
      (depth.core.read .rbp).toNat 8 := by
    rw [rdi, rbp]
    unfold RecursiveRelease.Return.StackSlotApart
    unfold SavedApart at mutexApart
    change slot + 8 ≤ base.toNat ∨ base.toNat + 16 ≤ slot
    change base.toNat + 20 ≤ slot ∨ slot + 8 ≤ base.toNat at mutexApart
    omega
  have targetVsMutex : RecursiveRelease.Return.StackSlotApart (depth.core.read .rdi).toNat
      (depth.core.read .rbp + 8#64).toNat 8 := by
    rw [rdi, targetAddress]
    exact targetMutexApart
  obtain ⟨final, tail, endpoint, result, rsp, restored, releaseFrame, fields⟩ :=
    RecursiveRelease.Return.private_release_return reached atAlign atLock atWrite
      (fetchFramed compare (codeSpan (by decide) (by decide)))
      (fetchFramed epilogue (codeSpan (by decide) (by decide))) atSlot atTarget slotVsMutex targetVsMutex
  rw [rdi] at releaseFrame fields
  refine ⟨final, ?_, endpoint, result, restored, ?_, ?_, ?_, fields⟩
  · change run Atomic9.step (20 + 17) initial = some final
    rw [run_add, entryRun]
    exact tail
  · rw [rsp, rbp, savedSlot, show 16#64 = 8#64 + 8#64 from rfl,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  · have stackFrame := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp frame
    have mutexFrame := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp releaseFrame
    exact (stackFrame.mono (fun _ h => Or.inl h)).trans (mutexFrame.mono (fun _ h => Or.inr h))
  · intro offset inside
    have exactLen : offset < (encodeWords [initial.core.read .rbp]).length := by
      simpa only [length_encodeWords_singleton] using inside
    have outside : slot + offset < base.toNat ∨ base.toNat + 16 ≤ slot + offset := by
      unfold SavedApart at mutexApart
      change base.toNat + 20 ≤ slot ∨ slot + 8 ≤ base.toNat at mutexApart
      omega
    rw [releaseFrame.2 _ outside, Memory.writeBytes_get wrote offset exactLen,
      List.getElem?_eq_getElem exactLen]

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn
