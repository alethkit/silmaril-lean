module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.StrLength.Defs
import Silmaril.X86.Ext.Lemmas

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.StrLength

open Silmaril.Elf.Corpus.SqliteNativeCompilers.StrLength
open Silmaril.X86
open Silmaril.Process (Memory)

private def tested (s : State) : State :=
  { s with flags := Ext.logicFlagsN (s.read .rdi), rip := s.rip + 3 }

private theorem testExec (s : State) (m : Memory) :
    Ext.exec (.test .q (.reg .rdi) .rdi) s m = .ok (tested s) m := by
  rw [Ext.exec_test_reg, BitVec.and_self, Ext.Sz.read_q]
  rfl

private theorem testedZero (s : State) :
    Ext.Cond.e.eval (tested s).flags = some (decide (s.read .rdi = 0#64)) := by
  change some (s.read .rdi == 0#64) = some (decide (s.read .rdi = 0#64))
  rw [Bool.beq_eq_decide_eq]

private def loadedLength (s : State) (value : BitVec 32) : State :=
  { s.write .rax (value.setWidth 64) with rip := s.rip + 3 }

private theorem loadExec (s : State) (m : Memory) (value : BitVec 32)
    (readable : Ext.loadN m (s.read .rdi + 24) 4 = some (value.setWidth 64)) :
    Ext.exec (.load .d .rax (Ext.Mem.ofReg .rdi none 24)) s m =
      .ok (loadedLength s value) m := by
  rw [Ext.exec_load]
  have addr (next : Word) : (Ext.Mem.ofReg .rdi none 24).addr s next = s.read .rdi + 24 := by
    simp [Ext.Mem.addr, Ext.Mem.ofReg]
  rw [addr, show Ext.Sz.d.bytes = 4 from rfl, readable]
  simp [loadedLength, Ext.Sz.write]
  rfl

private def zeroed (s : State) : State :=
  { s.write .rax 0 with flags := Ext.logicFlagsN (0 : BitVec 32), rip := s.rip + 2 }

private theorem xorExec (s : State) (m : Memory) :
    Ext.exec (.alu .d .xor (.reg .rax) .rax) s m = .ok (zeroed s) m := by
  rw [Ext.exec_alu_reg _ _ _ _ _ _ (by decide)]
  simp only [Ext.AluOp.flagsN, Ext.AluOp.resultN, BitVec.xor_self]
  rfl

private def afterBranch (s : State) (offset : BitVec 8) (taken : Bool) : State :=
  { s with rip := if taken then s.rip + 2 + offset.signExtend 64 else s.rip + 2 }

private theorem branchExec (s : State) (m : Memory) (offset : BitVec 8) :
    Ext.exec (.jcc8 .e offset) (tested s) m =
      .ok (afterBranch (tested s) offset (decide (s.read .rdi = 0#64))) m :=
  Ext.exec_jcc8 (tested s) m .e offset _ (testedZero s)

private theorem stackNotReturned (entry current : MState)
    (stack : current.core.read .rsp = entry.core.read .rsp) :
    ¬ FnContract.Returned Open.isa entry current := by
  intro h
  have same := stack.symm.trans h.2
  have : (0 : Word) = 8 := by
    simpa using congrArg (fun sp => sp - entry.core.read .rsp) same
  contradiction

private theorem returnFrom {entry current : MState} {base : Word} {code : List Byte}
    {offset : Nat} (loaded : Ext.Loaded entry.memory base code)
    (abi : FnContract.AbiEntry entry.core entry.memory)
    (memory : current.memory = entry.memory) (stack : current.core.read .rsp = entry.core.read .rsp)
    (atRet : current.core.rip = base + BitVec.ofNat 64 offset)
    (fit : offset + 1 ≤ code.length)
    (decode : Open.decode ((code.drop offset).take 1) = some (.base .ret, 1)) :
    ∃ final, FnContract.RunsIn Open.isa (fun s => ¬ FnContract.Returned Open.isa entry s) current final ∧
      FnContract.Returned Open.isa entry final ∧
      final.core.read .rax = current.core.read .rax ∧ final.memory = entry.memory := by
  let target := FnContract.retOf entry.core entry.memory
  let finalCore : State := { current.core.write .rsp (current.core.read .rsp + 8) with rip := target }
  let final : MState := ⟨finalCore, current.memory⟩
  have readable : current.memory.readBytes (current.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [target]) := by
    rw [memory, stack]
    exact abi.returnAddress
  have step : Open.step current = some final := by
    refine Open.step_of_listed (memory ▸ loaded) atRet fit decode ?_
    change Ext.exec .ret current.core current.memory = _
    simp [Ext.exec_ret, Silmaril.X86.Insn.exec, Silmaril.X86.popWord_of_readBytes readable, finalCore]
  exact ⟨final, .step (stackNotReturned entry current stack) step (.refl final),
    ⟨rfl, by simp [final, finalCore, stack]⟩, by simp [final, finalCore], memory⟩

private theorem gccReturns {entry : MState} {base : Word} {value : BitVec 32}
    (loaded : Ext.Loaded entry.memory base gccCode)
    (atEntry : entry.core.rip = base)
    (abi : FnContract.AbiEntry entry.core entry.memory)
    (readable : FieldReadable entry value) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧
      final.core.read .rax = (if entry.core.read .rdi = 0#64 then 0 else value.setWidth 64) ∧
      final.memory = entry.memory := by
  let afterXor : MState := ⟨zeroed entry.core, entry.memory⟩
  let afterTest : MState := ⟨tested afterXor.core, entry.memory⟩
  have stepXor : Open.step entry = some afterXor :=
    Open.step_of_listed (o := 0) (l := 2) (i := .base (.alu .d .xor (.reg .rax) .rax)) loaded (by simpa using atEntry)
      (by decide) (by decide +kernel) (xorExec entry.core entry.memory)
  have stepTest : Open.step afterXor = some afterTest :=
    Open.step_of_listed (o := 2) (l := 3) (i := .base (.test .q (.reg .rdi) .rdi)) loaded (by simp [afterXor, zeroed, atEntry])
      (by decide) (by decide +kernel) (testExec afterXor.core entry.memory)
  let taken := decide (entry.core.read .rdi = 0#64)
  let afterJump : MState := ⟨afterBranch afterTest.core 3 taken, entry.memory⟩
  have stepBranch : Open.step afterTest = some afterJump := by
    refine Open.step_of_listed (o := 5) (l := 2) (i := .base (.jcc8 .e 3)) loaded
      (by simp [afterTest, afterXor, tested, zeroed, atEntry, BitVec.add_assoc])
      (by decide) (by decide +kernel) ?_
    change Ext.exec (.jcc8 .e 3) afterTest.core entry.memory = _
    simpa [afterJump, afterTest, taken, afterXor, zeroed] using branchExec afterXor.core entry.memory 3
  have startPrefix {final : MState}
      (tail : FnContract.RunsIn Open.isa (fun s => ¬ FnContract.Returned Open.isa entry s)
        afterJump final) :
      FnContract.RunsIn Open.isa (fun s => ¬ FnContract.Returned Open.isa entry s) entry final :=
    .step (stackNotReturned entry entry rfl) stepXor
      (.step (stackNotReturned entry afterXor (by simp [afterXor, zeroed])) stepTest
        (.step (stackNotReturned entry afterTest (by simp [afterTest, afterXor, tested, zeroed]))
          stepBranch tail))
  by_cases null : entry.core.read .rdi = 0#64
  · have atRet : afterJump.core.rip = base + BitVec.ofNat 64 10 := by
      simp [afterJump, afterBranch, afterTest, afterXor, tested, zeroed, taken,
        null, atEntry, BitVec.add_assoc]
    obtain ⟨final, path, returned, result, frame⟩ := returnFrom loaded abi
      (current := afterJump) rfl (by simp [afterJump, afterBranch, afterTest, afterXor, tested, zeroed])
      atRet (by decide) (by decide +kernel)
    exact ⟨final, ⟨startPrefix path, returned⟩, result.trans (by
      simp [afterJump, afterBranch, afterTest, afterXor, tested, zeroed, null]), frame⟩
  · have atLoad : afterJump.core.rip = base + BitVec.ofNat 64 7 := by
      simp [afterJump, afterBranch, afterTest, afterXor, tested, zeroed, taken,
        null, atEntry, BitVec.add_assoc]
    let afterLoad : MState := ⟨loadedLength afterJump.core value, entry.memory⟩
    have stepLoad : Open.step afterJump = some afterLoad := by
      refine Open.step_of_listed (o := 7) (l := 3) (i := .base (.load .d .rax (Ext.Mem.ofReg .rdi none 24))) loaded atLoad (by decide) (by decide +kernel) ?_
      exact loadExec afterJump.core entry.memory value (by
        simpa [afterJump, afterBranch, afterTest, afterXor, tested, zeroed] using readable null)
    have atRet : afterLoad.core.rip = base + BitVec.ofNat 64 10 := by
      simp [afterLoad, loadedLength, atLoad, BitVec.add_assoc]
    obtain ⟨final, path, returned, result, frame⟩ := returnFrom loaded abi
      (current := afterLoad) rfl (by
        simp [afterLoad, loadedLength, afterJump, afterBranch, afterTest, afterXor, tested, zeroed])
      atRet (by decide) (by decide +kernel)
    have loadPath : FnContract.RunsIn Open.isa (fun s => ¬ FnContract.Returned Open.isa entry s)
        afterJump final := FnContract.RunsIn.step (stackNotReturned entry afterJump (by
      simp [afterJump, afterBranch, afterTest, afterXor, tested, zeroed])) stepLoad path
    exact ⟨final, ⟨startPrefix loadPath, returned⟩, result.trans (by simp [afterLoad, loadedLength, null]),
      frame⟩

private theorem clangReturns {entry : MState} {base : Word} {value : BitVec 32}
    (loaded : Ext.Loaded entry.memory base clangCode)
    (atEntry : entry.core.rip = base)
    (abi : FnContract.AbiEntry entry.core entry.memory)
    (readable : FieldReadable entry value) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧
      final.core.read .rax = (if entry.core.read .rdi = 0#64 then 0 else value.setWidth 64) ∧
      final.memory = entry.memory := by
  let afterTest : MState := ⟨tested entry.core, entry.memory⟩
  have stepTest : Open.step entry = some afterTest :=
    Open.step_of_listed (o := 0) (l := 3) (i := .base (.test .q (.reg .rdi) .rdi))
      loaded (by simpa using atEntry) (by decide) (by decide +kernel) (testExec entry.core entry.memory)
  let taken := decide (entry.core.read .rdi = 0#64)
  let afterJump : MState := ⟨afterBranch afterTest.core 4 taken, entry.memory⟩
  have stepBranch : Open.step afterTest = some afterJump := by
    refine Open.step_of_listed (o := 3) (l := 2) (i := .base (.jcc8 .e 4)) loaded
      (by simp [afterTest, tested, atEntry]) (by decide) (by decide +kernel) ?_
    exact branchExec entry.core entry.memory 4
  have jumpTail {middle final : MState} (step : Open.step afterJump = some middle)
      (tail : FnContract.RunsIn Open.isa (fun s => ¬ FnContract.Returned Open.isa entry s)
        middle final) :
      FnContract.RunsIn Open.isa (fun s => ¬ FnContract.Returned Open.isa entry s) entry final :=
    .step (stackNotReturned entry entry rfl) stepTest
      (.step (stackNotReturned entry afterTest rfl) stepBranch
        (.step (stackNotReturned entry afterJump rfl) step tail))
  by_cases null : entry.core.read .rdi = 0#64
  · have atXor : afterJump.core.rip = base + BitVec.ofNat 64 9 := by
      simp [afterJump, afterBranch, afterTest, tested, taken, null, atEntry, BitVec.add_assoc]
    let afterXor : MState := ⟨zeroed afterJump.core, entry.memory⟩
    have stepXor : Open.step afterJump = some afterXor :=
      Open.step_of_listed (o := 9) (l := 2) (i := .base (.alu .d .xor (.reg .rax) .rax))
        loaded atXor (by decide) (by decide +kernel) (xorExec afterJump.core entry.memory)
    have atRet : afterXor.core.rip = base + BitVec.ofNat 64 11 := by
      simp [afterXor, zeroed, atXor, BitVec.add_assoc]
    obtain ⟨final, path, returned, result, frame⟩ := returnFrom loaded abi
      (current := afterXor) rfl (by simp [afterXor, zeroed, afterJump, afterBranch, afterTest, tested])
      atRet (by decide) (by decide +kernel)
    exact ⟨final, ⟨jumpTail stepXor path, returned⟩, result.trans (by
      simp [afterXor, zeroed, null]), frame⟩
  · have atLoad : afterJump.core.rip = base + BitVec.ofNat 64 5 := by
      simp [afterJump, afterBranch, afterTest, tested, taken, null, atEntry, BitVec.add_assoc]
    let afterLoad : MState := ⟨loadedLength afterJump.core value, entry.memory⟩
    have stepLoad : Open.step afterJump = some afterLoad :=
      Open.step_of_listed (o := 5) (l := 3)
        (i := .base (.load .d .rax (Ext.Mem.ofReg .rdi none 24)))
        loaded atLoad (by decide) (by decide +kernel) (loadExec _ _ value (readable null))
    have atRet : afterLoad.core.rip = base + BitVec.ofNat 64 8 := by
      simp [afterLoad, loadedLength, atLoad, BitVec.add_assoc]
    obtain ⟨final, path, returned, result, frame⟩ := returnFrom loaded abi
      (current := afterLoad) rfl (by simp [afterLoad, loadedLength, afterJump, afterBranch, afterTest, tested])
      atRet (by decide) (by decide +kernel)
    exact ⟨final, ⟨jumpTail stepLoad path, returned⟩, result.trans (by
      simp [afterLoad, loadedLength, null]), frame⟩

theorem strLength_pair {gcc clang : MState} {gccBase clangBase : Word}
    {length : BitVec 32}
    (gccLoaded : Ext.Loaded gcc.memory gccBase gccCode)
    (clangLoaded : Ext.Loaded clang.memory clangBase clangCode)
    (gccEntry : gcc.core.rip = gccBase) (clangEntry : clang.core.rip = clangBase)
    (gccAbi : FnContract.AbiEntry gcc.core gcc.memory)
    (clangAbi : FnContract.AbiEntry clang.core clang.memory)
    (sameNull : gcc.core.read .rdi = 0#64 ↔ clang.core.read .rdi = 0#64)
    (gccField : FieldReadable gcc length)
    (clangField : FieldReadable clang length) :
    ∃ gccFinal clangFinal, FnContract.FirstReturn Open.isa gcc gccFinal ∧
      FnContract.FirstReturn Open.isa clang clangFinal ∧
      gccFinal.core.read .rax = (if gcc.core.read .rdi = 0#64 then 0 else length.setWidth 64) ∧
      clangFinal.core.read .rax = gccFinal.core.read .rax ∧
      gccFinal.memory = gcc.memory ∧ clangFinal.memory = clang.memory := by
  obtain ⟨g, gr, gv, gm⟩ := gccReturns gccLoaded gccEntry gccAbi gccField
  obtain ⟨c, cr, cv, cm⟩ := clangReturns clangLoaded clangEntry clangAbi clangField
  exact ⟨g, c, gr, cr, gv, by simp only [gv, cv, sameNull], gm, cm⟩

end Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.StrLength
