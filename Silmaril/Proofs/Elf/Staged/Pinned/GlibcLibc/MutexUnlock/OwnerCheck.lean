module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.X86.Atomic9.Thms
import Silmaril.X86.Ext.Lemmas

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck

open Silmaril.Elf Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck
open Silmaril.X86 Silmaril.X86.Ext
open Silmaril.Machine.Execution (run run_succ)

theorem code :
    CodeAt F 0xa1bf2 ownerBytes ∧
      MutexUnlock.entry.value ≤ 0xa1bf2 ∧
      0xa1bf2 + ownerBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel), by decide, by decide⟩

private def wrap (instruction : Ext.Instr) : Atomic9.Instr := .open9 (.ext8 (.base instruction))
private def tidMem : Ext.Mem := Ext.Mem.fsAt 0x2d0
private def ownerMem : Ext.Mem := Ext.Mem.ofReg .rdi none 8

theorem owner_check {initial : MState} {threadId owner : BitVec 32}
    (rip : initial.core.rip = 0xa1bf2)
    (loaded : Loaded initial.memory 0xa1bf2 ownerBytes)
    (threadRead : loadN initial.memory (initial.core.fsBase + 0x2d0#64) 4 =
      some (threadId.setWidth 64))
    (ownerRead : loadN initial.memory (initial.core.read .rdi + 8#64) 4 =
      some (owner.setWidth 64)) :
    ∃ final, run Atomic9.step 3 initial = some final ∧
      final.core.rip = (if owner = threadId then 0xa1c06 else 0xa1bff) ∧
      final.core.read .rax = threadId.setWidth 64 ∧
      (∀ reg, reg ≠ .rax → final.core.read reg = initial.core.read reg) ∧
      final.core.fsBase = initial.core.fsBase ∧ final.memory = initial.memory := by
  let loadedCore : State := {Sz.d.write initial.core .rax threadId with rip := 0xa1bfa}
  have issueLoad : Atomic9.exec (wrap (.load .d .rax tidMem)) initial.core initial.memory 8 =
      .ok loadedCore initial.memory := by
    have addr : tidMem.addr initial.core (initial.core.rip + 8#64) = initial.core.fsBase + 0x2d0#64 := by
      rw [show tidMem = Ext.Mem.fsAt 0x2d0 from rfl, Ext.Mem.addr_fsAt]
      rfl
    have read : readRM .d (.mem tidMem) initial.core initial.memory (initial.core.rip + 8#64) =
        some threadId := by
      simp only [readRM, addr, show Sz.d.bytes = 4 from rfl, threadRead, Option.map_some]
      simp
    change retire (initial.core.rip + 8#64)
      ((readRM .d (.mem tidMem) initial.core initial.memory (initial.core.rip + 8#64)).map
        (fun value => (Sz.d.write initial.core .rax value, initial.memory))) = _
    rw [read, rip]
    rfl
  have first : Atomic9.step initial = some ⟨loadedCore, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 0) (l := 8) loaded rip
      (by decide +kernel) (by decide +kernel) issueLoad
  let compared : State := {loadedCore with rip := 0xa1bfd, flags := subFlagsN owner threadId}
  have issueCompare : Atomic9.exec (wrap (.alu .d .cmp (.mem ownerMem) .rax)) loadedCore initial.memory 3 =
      .ok compared initial.memory := by
    have address : ownerMem.addr loadedCore (loadedCore.rip + 3#64) =
        initial.core.read .rdi + 8#64 := by
      simp [ownerMem, Ext.Mem.addr, Ext.Mem.ofReg, loadedCore, Sz.write, State.write, State.read]
    have memoryRead : readRM .d (.mem ownerMem) loadedCore initial.memory (loadedCore.rip + 3#64) =
        some owner := by
      simp only [readRM, address, show Sz.d.bytes = 4 from rfl, ownerRead, Option.map_some]
      simp
    have tid : Sz.d.read loadedCore .rax = threadId := by
      simp [Sz.read, loadedCore, Sz.write, State.write, State.read]
    change retire (loadedCore.rip + 3#64)
      (aluStep .d .cmp (.mem ownerMem) (Sz.d.read loadedCore .rax) loadedCore initial.memory
        (loadedCore.rip + 3#64)) = _
    simp only [aluStep, memoryRead, tid, AluOp.flagsN, ite_true, retire]
    rfl
  have second : Atomic9.step ⟨loadedCore, initial.memory⟩ = some ⟨compared, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 8) (l := 3) (m := ⟨loadedCore, initial.memory⟩)
      loaded rfl (by decide +kernel) (by decide +kernel) issueCompare
  let final : State := {compared with rip := if owner = threadId then 0xa1c06 else 0xa1bff}
  have cond : Cond.e.eval compared.flags = some (owner == threadId) := by
    change some (owner - threadId == 0#32) = _
    by_cases same : owner = threadId
    · simp [same]
    · have nonzero : owner - threadId ≠ 0#32 := by
        intro zero
        apply same
        bv_omega
      simp [beq_eq_false_iff_ne.mpr nonzero, beq_eq_false_iff_ne.mpr same]
  have branch : Atomic9.exec (wrap (.jcc8 .e 7)) compared initial.memory 2 =
      .ok final initial.memory := by
    change Ext.exec (.jcc8 .e 7) compared initial.memory = _
    rw [exec_jcc8 _ _ _ _ _ cond]
    by_cases same : owner = threadId
    · simp only [same, beq_self_eq_true, ite_true, final]
      rfl
    · simp only [beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, ite_false, final, same]
      rfl
  have third : Atomic9.step ⟨compared, initial.memory⟩ = some ⟨final, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 11) (l := 2) (m := ⟨compared, initial.memory⟩)
      loaded rfl (by decide +kernel) (by decide +kernel) branch
  refine ⟨⟨final, initial.memory⟩, ?_, rfl, ?_, ?_, rfl, rfl⟩
  · simp [run_succ, first, second, third]
  · simp [final, compared, loadedCore, Sz.write, State.write, State.read]
  · intro reg other
    simp [final, compared, loadedCore, Sz.write, State.write, State.read, other]

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck
