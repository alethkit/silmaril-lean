module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return.Defs
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Thms
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ReleaseReturn

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.X86
open Silmaril.X86.Ext (Loaded leBytes)
open Silmaril.Machine.Execution (run run_add)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Process (Memory)
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return

theorem private_release_return {initial : MState} {kind users : BitVec 32} {savedFrame target : Word}
    (entry : RecursiveRelease.Entry initial kind users)
    (aligned : (initial.core.read .rdi).toNat % 4 = 0)
    (lock : initial.memory.readBytes (initial.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : initial.memory.Permitted .write (initial.core.read .rdi).toNat 4)
    (compare : Loaded initial.memory 0xa1ba4 NoWakeReturn.compareBytes)
    (epilogue : Loaded initial.memory 0xa1b94 NoWakeReturn.returnBytes)
    (saved : initial.memory.readBytes (initial.core.read .rbp).toNat 8 = some (encodeWords [savedFrame]))
    (targetSlot : initial.memory.readBytes (initial.core.read .rbp + 8#64).toNat 8 =
      some (encodeWords [target]))
    (savedApart : StackSlotApart (initial.core.read .rdi).toNat (initial.core.read .rbp).toNat 8)
    (targetApart : StackSlotApart (initial.core.read .rdi).toNat (initial.core.read .rbp + 8#64).toNat 8) :
    ∃ final, run Atomic9.step 17 initial = some final ∧
      final.core.rip = target ∧ final.core.read .rax = 0#64 ∧
      final.core.read .rsp = initial.core.read .rbp + 16#64 ∧ final.core.read .rbp = savedFrame ∧
      initial.memory.WritesOnly final.memory (initial.core.read .rdi).toNat 16 ∧
      ∀ offset, offset < 4 →
        let base := (initial.core.read .rdi).toNat
        final.memory.bytes.get? (base + offset) = some 0 ∧
        final.memory.bytes.get? (base + 4 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 8 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 12 + offset) =
          (leBytes ((users - 1#32).setWidth 64) 4)[offset]? := by
  obtain ⟨released, releaseRun, rip, rax, rbp, frame, lockBytes, fields⟩ :=
    RecursiveRelease.private_through_exchange_sc_fields_with_rbp entry aligned lock writable
  let mutex := (initial.core.read .rdi).toNat
  have readFramed {address size : Nat} (access : Silmaril.Process.Access)
      (apart : StackSlotApart mutex address size) :
      released.memory.readWith access address size = initial.memory.readWith access address size := by
    unfold StackSlotApart at apart
    exact Silmaril.X86.Memory.readWith_writesOnly frame access address size apart
  have codeApart := entry.codeApart
  change mutex + 16 ≤ 0xa1b6f ∨ 0xa1c10 ≤ mutex + 4 at codeApart
  have compareFramed : Loaded released.memory 0xa1ba4 NoWakeReturn.compareBytes := by
    unfold Loaded Memory.fetchBytes at compare ⊢
    rw [readFramed]
    · exact compare
    · change StackSlotApart mutex 0xa1ba4 5
      unfold StackSlotApart
      omega
  have epilogueFramed : Loaded released.memory 0xa1b94 NoWakeReturn.returnBytes := by
    unfold Loaded Memory.fetchBytes at epilogue ⊢
    rw [readFramed]
    · exact epilogue
    · change StackSlotApart mutex 0xa1b94 5
      unfold StackSlotApart
      omega
  have savedFramed : released.memory.readBytes (released.core.read .rbp).toNat 8 =
      some (encodeWords [savedFrame]) := by
    rw [rbp, Memory.readBytes, readFramed .read savedApart]
    exact saved
  have targetFramed : released.memory.readBytes (released.core.read .rbp + 8#64).toNat 8 =
      some (encodeWords [target]) := by
    rw [rbp, Memory.readBytes, readFramed .read targetApart]
    exact targetSlot
  obtain ⟨final, returnRun, endpoint, result, rsp, restored, _, memory⟩ :=
    NoWakeReturn.no_wake_return rip rax compareFramed epilogueFramed savedFramed targetFramed
  refine ⟨final, ?_, endpoint, result, rsp.trans (congrArg (· + 16#64) rbp), restored,
    memory.symm ▸ frame, ?_⟩
  · change run Atomic9.step (11 + 6) initial = some final
    rw [run_add, releaseRun]
    exact returnRun
  · intro offset within
    rw [memory]
    obtain ⟨depth, owner, count⟩ := fields offset within
    exact ⟨lockBytes (mutex + offset) (by dsimp [mutex]; omega) (by dsimp [mutex]; omega),
      depth, owner, count⟩

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ReleaseReturn
