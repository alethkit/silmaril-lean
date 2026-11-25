module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.X86.Atomic9.Thms
import Silmaril.X86.Ext.Lemmas

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn

open Silmaril.Elf Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn
open Silmaril.X86 Silmaril.X86.Ext
open Silmaril.Machine.Execution
open Silmaril.Machine.LittleEndian (encodeWords)

theorem code :
    CodeAt F 0xa1ba4 compareBytes ∧ CodeAt F 0xa1b94 returnBytes ∧
      MutexUnlock.entry.value ≤ 0xa1b94 ∧
      0xa1ba4 + compareBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
      (by decide +kernel) (by decide +kernel),
    codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
      (by decide +kernel) (by decide +kernel),
    by decide, by decide⟩

private def wrap (instr : Ext.Instr) : Atomic9.Instr := .open9 (.ext8 (.base instr))

theorem no_wake_return {initial : MState} {savedFrame target : Word}
    (rip : initial.core.rip = 0xa1ba4)
    (old : initial.core.read .rax = 1#64)
    (compareLoaded : Loaded initial.memory 0xa1ba4 compareBytes)
    (returnLoaded : Loaded initial.memory 0xa1b94 returnBytes)
    (saved : initial.memory.readBytes (initial.core.read .rbp).toNat 8 =
      some (encodeWords [savedFrame]))
    (returnSlot : initial.memory.readBytes (initial.core.read .rbp + 8#64).toNat 8 =
      some (encodeWords [target])) :
    ∃ final, run Atomic9.step 6 initial = some final ∧
      final.core.rip = target ∧ final.core.read .rax = 0#64 ∧
      final.core.read .rsp = initial.core.read .rbp + 16#64 ∧
      final.core.read .rbp = savedFrame ∧
      (∀ reg, reg ≠ .rax → reg ≠ .rsp → reg ≠ .rbp →
        final.core.read reg = initial.core.read reg) ∧
      final.memory = initial.memory := by
  let cmp : State := {initial.core with rip := 0xa1ba7, flags := subFlagsN 1#32 1#32}
  have execCmp : Atomic9.exec (wrap (.aluI8 .d .cmp (.reg .rax) 1))
      initial.core initial.memory 3 = .ok cmp initial.memory := by
    change Ext.exec (.aluI8 .d .cmp (.reg .rax) 1) initial.core initial.memory = _
    rw [exec_cmpI8_reg, rip]
    simp [cmp, Sz.read, old]
    decide +kernel
  have first : Atomic9.step initial = some ⟨cmp, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 0) (l := 3) compareLoaded rip
      (by decide +kernel) (by decide +kernel) execCmp
  let branch : State := {cmp with rip := 0xa1b94}
  have cond : Cond.le.eval cmp.flags = some true := by
    change Cond.le.eval (subFlagsN 1#32 1#32) = some true
    decide +kernel
  have execBranch : Atomic9.exec (wrap (.jcc8 .le 0xeb)) cmp initial.memory 2 =
      .ok branch initial.memory := by
    change Ext.exec (.jcc8 .le 0xeb) cmp initial.memory = _
    rw [exec_jcc8 _ _ _ _ _ cond]
    have destination : (0xa1ba7 : Word) + BitVec.ofNat 64 (Instr.jcc8 .le 0xeb).length +
        (0xeb : BitVec 8).signExtend 64 = 0xa1b94 := by decide +kernel
    simp only [ite_true, show cmp.rip = 0xa1ba7 from rfl, destination, branch]
  have second : Atomic9.step ⟨cmp, initial.memory⟩ = some ⟨branch, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 3) (l := 2) (m := ⟨cmp, initial.memory⟩) compareLoaded rfl
      (by decide +kernel) (by decide +kernel) execBranch
  let nop : State := {branch with rip := 0xa1b95}
  have third : Atomic9.step ⟨branch, initial.memory⟩ = some ⟨nop, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 0) (l := 1) (i := wrap (.nop 0))
      (m := ⟨branch, initial.memory⟩) returnLoaded rfl (by decide +kernel) (by decide +kernel) rfl
  let cleared : State := {Sz.d.write nop .rax 0#32 with rip := 0xa1b97, flags := logicFlagsN 0#32}
  have execClear : Atomic9.exec (wrap (.alu .d .xor (.reg .rax) .rax)) nop initial.memory 2 =
      .ok cleared initial.memory := by
    change Ext.exec (.alu .d .xor (.reg .rax) .rax) nop initial.memory = _
    rw [exec_alu_reg _ _ _ _ _ _ (by decide)]
    simp only [AluOp.resultN, AluOp.flagsN, BitVec.xor_self]
    rfl
  have fourth : Atomic9.step ⟨nop, initial.memory⟩ = some ⟨cleared, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 1) (l := 2) (m := ⟨nop, initial.memory⟩) returnLoaded rfl
      (by decide +kernel) (by decide +kernel) execClear
  let frame := initial.core.read .rbp
  let setFrame := cleared.write .rsp (cleared.read .rbp)
  have setSp : setFrame.read .rsp = frame := by
    simp [setFrame, frame, cleared, nop, branch, cmp, Sz.write, State.write, State.read]
  let leave : State := { (setFrame.write .rsp (setFrame.read .rsp + 8#64)).write .rbp savedFrame with
    rip := 0xa1b98 }
  have execLeave : Atomic9.exec (wrap .leave) cleared initial.memory 1 =
      .ok leave initial.memory := by
    change Ext.exec .leave cleared initial.memory = _
    have handled := popWord_of_readBytes (s := setFrame) (by simpa only [setSp] using saved)
    rw [exec_leave, handled]
    rfl
  have fifth : Atomic9.step ⟨cleared, initial.memory⟩ = some ⟨leave, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 3) (l := 1) (m := ⟨cleared, initial.memory⟩) returnLoaded rfl
      (by decide +kernel) (by decide +kernel) execLeave
  let finalCore : State := { leave.write .rsp (frame + 16#64) with rip := target }
  have execRet : Atomic9.exec (wrap .ret) leave initial.memory 1 = .ok finalCore initial.memory := by
    change Ext.exec .ret leave initial.memory = _
    rw [exec_ret]
    simp only [Insn.exec]
    have sp : leave.read .rsp = frame + 8#64 := by
      have raw : setFrame.regs .rsp = frame := setSp
      simp [leave, raw, State.write, State.read]
    have handled := popWord_of_readBytes (s := leave) (by simpa only [sp] using returnSlot)
    rw [handled, sp, BitVec.add_assoc]
    rfl
  have sixth : Atomic9.step ⟨leave, initial.memory⟩ = some ⟨finalCore, initial.memory⟩ :=
    Atomic9.step_of_listed (o := 4) (l := 1) (m := ⟨leave, initial.memory⟩) returnLoaded rfl
      (by decide +kernel) (by decide +kernel) execRet
  refine ⟨⟨finalCore, initial.memory⟩, ?_, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · simp [run_succ, first, second, third, fourth, fifth, sixth]
  · simp [finalCore, leave, setFrame, cleared, Sz.write, State.write, State.read]
  · simp [finalCore, frame, State.write, State.read]
  · simp [finalCore, leave, State.write, State.read]
  · intro reg noRax noRsp noRbp
    simp [finalCore, leave, setFrame, cleared, Sz.write, State.write, State.read, nop, branch, cmp,
      noRax, noRsp, noRbp]

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn
