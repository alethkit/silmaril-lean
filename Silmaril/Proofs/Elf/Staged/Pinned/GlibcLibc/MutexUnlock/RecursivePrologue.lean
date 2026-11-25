module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.X86.Atomic9.Thms
import Silmaril.X86.Ext.Lemmas

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue

open Silmaril.Elf Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue
open Silmaril.X86 Silmaril.X86.Ext
open Silmaril.Machine.Execution (run run_succ)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Process (Memory)

theorem code :
    CodeAt F 0xa1b50 codeBytes ∧ MutexUnlock.entry.value = 0xa1b50 ∧
      codeBytes.length ≤ MutexUnlock.entry.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel), by decide, by decide⟩

private def wrap (instruction : Ext.Instr) : Atomic9.Instr := .open9 (.ext8 (.base instruction))
private def kindMem : Ext.Mem := Ext.Mem.ofReg .rdi none 16

theorem recursive_prologue {initial : MState}
    (rip : initial.core.rip = 0xa1b50)
    (loaded : Loaded initial.memory 0xa1b50 codeBytes)
    (kind : loadN initial.memory (initial.core.read .rdi + 16#64) 4 = some 1#64)
    (writable : initial.memory.Permitted .write (initial.core.read .rsp - 8#64).toNat 8)
    (apart : (initial.core.read .rsp - 8#64).toNat + 8 ≤ 0xa1b50 ∨
      0xa1b6f ≤ (initial.core.read .rsp - 8#64).toNat) :
    ∃ final, run Atomic9.step 11 initial = some final ∧ final.core.rip = 0xa1bd0 ∧
      final.core.read .rax = 1 ∧ final.core.read .rdx = 1 ∧
      final.core.read .rbp = initial.core.read .rsp - 8#64 ∧
      final.core.read .rsp = initial.core.read .rsp - 8#64 - 16#64 ∧
      (∀ reg, reg ≠ .rax → reg ≠ .rdx → reg ≠ .rsp → reg ≠ .rbp →
        final.core.read reg = initial.core.read reg) ∧ final.core.fsBase = initial.core.fsBase ∧
      initial.memory.writeBytes (initial.core.read .rsp - 8#64).toNat
        (encodeWords [initial.core.read .rbp]) = some final.memory ∧
      initial.memory.WritesOnly final.memory (initial.core.read .rsp - 8#64).toNat 8 := by
  let s1 : State := {initial.core with rip := 0xa1b54}
  have first : Atomic9.step initial = some ⟨s1, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 0) (l := 4) (i := wrap .endbr64) loaded rip
      (by decide +kernel) (by decide +kernel) (by
        change Ext.exec .endbr64 initial.core initial.memory = _
        rw [exec_endbr64, rip]
        rfl)
  let s2 : State := {Sz.d.write s1 .rax 1#32 with rip := 0xa1b57}
  have issueLoad : Atomic9.exec (wrap (.load .d .rax kindMem)) s1 initial.memory 3 =
      .ok s2 initial.memory := by
    have address : kindMem.addr s1 (s1.rip + 3#64) = initial.core.read .rdi + 16#64 := by
      simp [kindMem, Ext.Mem.addr, Ext.Mem.ofReg, s1]
    have read : readRM .d (.mem kindMem) s1 initial.memory (s1.rip + 3#64) = some 1#32 := by
      simp [readRM, address, kind, Sz.bytes]
    change retire (s1.rip + 3#64)
      ((readRM .d (.mem kindMem) s1 initial.memory (s1.rip + 3#64)).map
        (fun value => (Sz.d.write s1 .rax value, initial.memory))) = _
    rw [read]
    rfl
  have second : Atomic9.step ⟨s1, initial.memory⟩ = some ⟨s2, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 4) (l := 3) (m := ⟨s1, initial.memory⟩) loaded rfl
      (by decide +kernel) (by decide +kernel) issueLoad
  let s3 : State := {Sz.d.write s2 .rdx 1#32 with rip := 0xa1b59}
  have third : Atomic9.step ⟨s2, initial.memory⟩ = some ⟨s3, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 7) (l := 2) (i := wrap (.mov .d (.reg .rdx) .rax))
      (m := ⟨s2, initial.memory⟩) loaded rfl (by decide +kernel) (by decide +kernel) rfl
  let s4 : State := {Sz.d.write s3 .rdx 1#32 with rip := 0xa1b5f, flags := logicFlagsN 1#32}
  have issueMask : Atomic9.exec (wrap (.aluI .d .and (.reg .rdx) 0x17f)) s3 initial.memory 6 =
      .ok s4 initial.memory := by
    change Ext.exec (.aluI .d .and (.reg .rdx) 0x17f) s3 initial.memory = _
    rw [exec_aluI_reg _ _ _ _ _ _ (by decide)]
    have argument : Sz.d.read s3 .rdx = 1#32 := by
      simp [s3, Sz.read, Sz.write, State.read, State.write]
    rw [argument]
    rfl
  have fourth : Atomic9.step ⟨s3, initial.memory⟩ = some ⟨s4, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 9) (l := 6) (i := wrap (.aluI .d .and (.reg .rdx) 0x17f))
      (m := ⟨s3, initial.memory⟩) loaded rfl (by decide +kernel) (by decide +kernel) issueMask
  let s5 : State := {s4 with rip := 0xa1b61, flags := logicFlagsN 0#8}
  have issueTest : Atomic9.exec (wrap (.testA8 0x7c)) s4 initial.memory 2 =
      .ok s5 initial.memory := by
    change Ext.exec (.testA8 0x7c) s4 initial.memory = _
    rw [exec_testA8]
    have value : (s4.read .rax).setWidth 8 = 1#8 := by
      simp [s4, s3, s2, Sz.write, State.read, State.write]
    rw [value]
    rfl
  have fifth : Atomic9.step ⟨s4, initial.memory⟩ = some ⟨s5, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 15) (l := 2) (i := wrap (.testA8 0x7c))
      (m := ⟨s4, initial.memory⟩) loaded rfl (by decide +kernel) (by decide +kernel) issueTest
  let s6 : State := {s5 with rip := 0xa1b63}
  have sixth : Atomic9.step ⟨s5, initial.memory⟩ = some ⟨s6, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 17) (l := 2) (i := wrap (.jcc8 .ne 0x5d))
      (m := ⟨s5, initial.memory⟩) loaded rfl (by decide +kernel) (by decide +kernel) rfl
  let slot := initial.core.read .rsp - 8#64
  let memory := {initial.memory with
    bytes := Memory.install initial.memory.bytes slot.toNat (encodeWords [initial.core.read .rbp])}
  have push : pushWord s6 initial.memory (s6.read .rbp) =
      some (s6.write .rsp slot, memory) := pushWord_eq_some writable
  have stored : initial.memory.writeBytes slot.toNat (encodeWords [initial.core.read .rbp]) =
      some memory := by
    have allowed : initial.memory.checkSpan .write slot.toNat 8 = true := writable
    simp only [Memory.writeBytes, length_encodeWords_singleton, allowed, ite_true, memory]
  have frame : initial.memory.WritesOnly memory slot.toNat 8 := by
    simpa only [length_encodeWords_singleton] using Memory.writeBytes_writesOnly stored
  have loadedAfter : Loaded memory 0xa1b50 codeBytes := by
    unfold Loaded Memory.fetchBytes at loaded ⊢
    rw [Silmaril.X86.Memory.readWith_writesOnly frame .execute _ _ (by
      change 0xa1b6f ≤ slot.toNat ∨ slot.toNat + 8 ≤ 0xa1b50
      exact apart.symm)]
    exact loaded
  let s7 : State := {s6.write .rsp slot with rip := 0xa1b64}
  have issuePush : Atomic9.exec (wrap (.push .rbp)) s6 initial.memory 1 = .ok s7 memory := by
    change Ext.exec (.push .rbp) s6 initial.memory = _
    rw [exec_push]
    simp only [Insn.exec, push, Option.map_some]
    rfl
  have seventh : Atomic9.step ⟨s6, initial.memory⟩ = some ⟨s7, memory⟩ :=
    Atomic9.step_of_listed (o := 19) (l := 1) (m := ⟨s6, initial.memory⟩) loaded rfl
      (by decide +kernel) (by decide +kernel) issuePush
  let s8 : State := {s7.write .rbp slot with rip := 0xa1b67}
  have eighth : Atomic9.step ⟨s7, memory⟩ = some ⟨s8, memory⟩ :=
    Atomic9.step_of_listed (o := 20) (l := 3) (i := wrap (.mov .q (.reg .rbp) .rsp))
      (m := ⟨s7, memory⟩) loadedAfter rfl (by decide +kernel) (by decide +kernel) rfl
  let s9 : State := {s8.write .rsp (slot - 16#64) with
    rip := 0xa1b6b, flags := subFlagsN slot 16#64}
  have ninth : Atomic9.step ⟨s8, memory⟩ = some ⟨s9, memory⟩ :=
    Atomic9.step_of_listed (o := 23) (l := 4) (i := wrap (.aluI8 .q .sub (.reg .rsp) 16))
      (m := ⟨s8, memory⟩) loadedAfter rfl (by decide +kernel) (by decide +kernel) rfl
  let s10 : State := {s9 with rip := 0xa1b6d, flags := logicFlagsN 1#32}
  have issueDispatchTest : Atomic9.exec (wrap (.test .d (.reg .rdx) .rdx)) s9 memory 2 =
      .ok s10 memory := by
    change Ext.exec (.test .d (.reg .rdx) .rdx) s9 memory = _
    rw [exec_test_reg]
    have value : Sz.d.read s9 .rdx = 1#32 := by
      simp [s9, s8, s7, s6, s5, s4, Sz.read, Sz.write, State.read, State.write]
    rw [value]
    rfl
  have tenth : Atomic9.step ⟨s9, memory⟩ = some ⟨s10, memory⟩ :=
    Atomic9.step_of_listed (o := 27) (l := 2) (i := wrap (.test .d (.reg .rdx) .rdx))
      (m := ⟨s9, memory⟩) loadedAfter rfl (by decide +kernel) (by decide +kernel) issueDispatchTest
  let s11 : State := {s10 with rip := 0xa1bd0}
  have eleventh : Atomic9.step ⟨s10, memory⟩ = some ⟨s11, memory⟩ :=
    Atomic9.step_of_listed (o := 29) (l := 2) (i := wrap (.jcc8 .ne 0x61))
      (m := ⟨s10, memory⟩) loadedAfter rfl (by decide +kernel) (by decide +kernel) rfl
  refine ⟨⟨s11, memory⟩, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, stored, frame⟩
  · simp [run_succ, first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh]
  · intro reg notA notD notSp notBp
    simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Sz.write, State.write, State.read,
      notA, notD, notSp, notBp]

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue
