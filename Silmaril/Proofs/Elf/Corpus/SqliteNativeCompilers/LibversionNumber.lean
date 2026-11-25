module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.Defs
import Silmaril.X86.Ext.Lemmas

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers

open Silmaril.Elf.Corpus.SqliteNativeCompilers (libversionNumberCode)
open Silmaril.X86

theorem libversionNumber_firstReturn {entry : MState} {base : Word}
    (loaded : Ext.Loaded entry.memory base libversionNumberCode)
    (atEntry : entry.core.rip = base)
    (abi : FnContract.AbiEntry entry.core entry.memory) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧
      FnContract.AbiReturn entry.core entry.memory final.core ∧
      final.core.read .rax = 3054001 ∧ final.memory = entry.memory := by
  let moved : State := { entry.core.write .rax 3054001 with rip := entry.core.rip + 5 }
  let middle : MState := ⟨moved, entry.memory⟩
  let returnAddress := FnContract.retOf entry.core entry.memory
  let final : MState := ⟨{ moved.write .rsp (moved.read .rsp + 8) with rip := returnAddress },
    entry.memory⟩
  have movedStack : moved.read .rsp = entry.core.read .rsp := by simp [moved]
  have stepMov : Open.step entry = some middle := by
    refine Open.step_of_listed (o := 0) (l := 5) (i := .base (.movI32 .rax 3054001))
      loaded (by simpa using atEntry) (by decide) (by decide +kernel) ?_
    change Ext.exec (.movI32 .rax 3054001) entry.core entry.memory = _
    rw [Ext.exec_movI32]
    rfl
  have stepRet : Open.step middle = some final := by
    refine Open.step_of_listed (o := 5) (l := 1) (i := .base .ret)
      loaded (by simp [middle, moved, atEntry]) (by decide) (by decide +kernel) ?_
    have readable : entry.memory.readBytes (moved.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [returnAddress]) := by
      rw [movedStack]
      exact abi.returnAddress
    change Ext.exec .ret moved entry.memory = _
    simp [Ext.exec_ret, Silmaril.X86.Insn.exec, Silmaril.X86.popWord_of_readBytes readable]
  have stackChanges : entry.core.read .rsp ≠ entry.core.read .rsp + 8#64 := by
    intro h
    have : (0 : BitVec 64) = 8 := by
      simpa using congrArg (fun sp => sp - entry.core.read .rsp) h
    contradiction
  have beforeMov : ¬ FnContract.Returned Open.isa entry entry := fun h => stackChanges h.2
  have beforeRet : ¬ FnContract.Returned Open.isa entry middle := fun h =>
    stackChanges (movedStack ▸ h.2)
  have returnAbi : FnContract.AbiReturn entry.core entry.memory final.core := by
    refine ⟨rfl, by simp [final, movedStack], ?_⟩
    intro reg saved
    have different : reg ≠ .rsp ∧ reg ≠ .rax := by
      revert saved reg
      decide
    simp [final, moved, State.read_write_other, different.1, different.2]
  exact ⟨final, ⟨.step beforeMov stepMov (.step beforeRet stepRet (.refl final)),
    returnAbi.pc, returnAbi.stack⟩, returnAbi, by simp [final, moved], rfl⟩

end Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers
