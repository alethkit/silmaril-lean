module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.X86.Atomic9.Thms
import Silmaril.X86.Ext.Lemmas

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch

open Silmaril.Elf Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch
open Silmaril.X86 Silmaril.X86.Ext
open Silmaril.Machine.Execution (run run_succ)

theorem code :
    CodeAt F 0xa1bd0 dispatchBytes ∧ CodeAt F 0xa1be7 recursiveBytes ∧
      MutexUnlock.entry.value ≤ 0xa1bd0 ∧
      0xa1be7 + recursiveBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
      (by decide +kernel) (by decide +kernel),
    codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
      (by decide +kernel) (by decide +kernel), by decide, by decide⟩

private def wrap (instruction : Ext.Instr) : Atomic9.Instr := .open9 (.ext8 (.base instruction))
private def kindMem : Ext.Mem := Ext.Mem.ofReg .rdi none 16

theorem recursive_dispatch {initial : MState}
    (rip : initial.core.rip = 0xa1bd0)
    (edx : initial.core.read .rdx = 1#64)
    (dispatch : Loaded initial.memory 0xa1bd0 dispatchBytes)
    (recursive : Loaded initial.memory 0xa1be7 recursiveBytes)
    (kind : loadN initial.memory (initial.core.read .rdi + 16#64) 4 = some 1#64) :
    ∃ final, run Atomic9.step 6 initial = some final ∧ final.core.rip = 0xa1bf2 ∧
      final.core.read .rax = 1#64 ∧
      (∀ reg, reg ≠ .rax → final.core.read reg = initial.core.read reg) ∧
      final.core.fsBase = initial.core.fsBase ∧ final.memory = initial.memory := by
  let s1 : State := {initial.core with rip := 0xa1bd6, flags := subFlagsN 1#32 256#32}
  have issueCompare : Atomic9.exec (wrap (.aluI .d .cmp (.reg .rdx) 256))
      initial.core initial.memory 6 = .ok s1 initial.memory := by
    change Ext.exec (.aluI .d .cmp (.reg .rdx) 256) initial.core initial.memory = _
    rw [exec_cmpI_reg, rip]
    simp [s1, Sz.read, edx]
    decide +kernel
  have first : Atomic9.step initial = some ⟨s1, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 0) (l := 6) dispatch rip
      (by decide +kernel) (by decide +kernel) issueCompare
  let s2 : State := {s1 with rip := 0xa1be7}
  have second : Atomic9.step ⟨s1, initial.memory⟩ = some ⟨s2, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 6) (l := 2) (i := wrap (.jcc8 .ne 0x0f))
      (m := ⟨s1, initial.memory⟩) dispatch rfl (by decide +kernel) (by decide +kernel) rfl
  let s3 : State := {Sz.d.write s2 .rax 1#32 with rip := 0xa1bea}
  have issueLoad : Atomic9.exec (wrap (.load .d .rax kindMem)) s2 initial.memory 3 =
      .ok s3 initial.memory := by
    have address : kindMem.addr s2 (s2.rip + 3#64) = initial.core.read .rdi + 16#64 := by
      simp [kindMem, Ext.Mem.addr, Ext.Mem.ofReg, s1, s2]
    have read : readRM .d (.mem kindMem) s2 initial.memory (s2.rip + 3#64) = some 1#32 := by
      simp [readRM, address, kind, Sz.bytes]
    change retire (s2.rip + 3#64)
      ((readRM .d (.mem kindMem) s2 initial.memory (s2.rip + 3#64)).map
        (fun value => (Sz.d.write s2 .rax value, initial.memory))) = _
    rw [read]
    rfl
  have third : Atomic9.step ⟨s2, initial.memory⟩ = some ⟨s3, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 0) (l := 3) (m := ⟨s2, initial.memory⟩) recursive rfl
      (by decide +kernel) (by decide +kernel) issueLoad
  let s4 : State := {Sz.d.write s3 .rax 1#32 with rip := 0xa1bed, flags := logicFlagsN 1#32}
  have issueMask : Atomic9.exec (wrap (.aluI8 .d .and (.reg .rax) 0x7f)) s3 initial.memory 3 =
      .ok s4 initial.memory := by
    change Ext.exec (.aluI8 .d .and (.reg .rax) 0x7f) s3 initial.memory = _
    rw [exec_aluI8_reg _ _ _ _ _ _ (by decide)]
    have argument : Sz.d.read s3 .rax = 1#32 := by
      simp [s3, Sz.read, Sz.write, State.read, State.write]
    rw [argument]
    rfl
  have fourth : Atomic9.step ⟨s3, initial.memory⟩ = some ⟨s4, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 3) (l := 3) (m := ⟨s3, initial.memory⟩) recursive rfl
      (by decide +kernel) (by decide +kernel) issueMask
  let s5 : State := {s4 with rip := 0xa1bf0, flags := subFlagsN 1#32 1#32}
  have issueTypeCompare : Atomic9.exec (wrap (.aluI8 .d .cmp (.reg .rax) 1)) s4 initial.memory 3 =
      .ok s5 initial.memory := by
    change Ext.exec (.aluI8 .d .cmp (.reg .rax) 1) s4 initial.memory = _
    rw [exec_cmpI8_reg]
    have argument : Sz.d.read s4 .rax = 1#32 := by
      simp [s4, Sz.read, Sz.write, State.read, State.write]
    rw [argument]
    rfl
  have fifth : Atomic9.step ⟨s4, initial.memory⟩ = some ⟨s5, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 6) (l := 3) (m := ⟨s4, initial.memory⟩) recursive rfl
      (by decide +kernel) (by decide +kernel) issueTypeCompare
  let s6 : State := {s5 with rip := 0xa1bf2}
  have sixth : Atomic9.step ⟨s5, initial.memory⟩ = some ⟨s6, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 9) (l := 2) (i := wrap (.jcc8 .ne 0x22))
      (m := ⟨s5, initial.memory⟩) recursive rfl (by decide +kernel) (by decide +kernel) rfl
  refine ⟨⟨s6, initial.memory⟩, ?_, rfl, rfl, ?_, rfl, rfl⟩
  · simp [run_succ, first, second, third, fourth, fifth, sixth]
  · intro reg other
    simp [s6, s5, s4, s3, s2, s1, Sz.write, State.write, State.read, other]

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch
