module

public import Silmaril.Machine.Region.X86.SqliteStrLength.Defs
public import Silmaril.X86.Open.Thms
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Ext.Lemmas

@[expose] public section
namespace Silmaril.Proofs.Machine.Region.X86.SqliteStrLength

open Silmaril.Machine.Region.X86.SqliteStrLength
open Silmaril.X86
open Silmaril.Process (Memory addressLimit)
open Silmaril.SSA.LambdaRTL
open Silmaril.Machine.Execution (run)

private def afterXor (entry : MState) : MState :=
  let before := Ext.Sz.d.read entry.core .rax
  ⟨{ entry.core.write .rax 0 with
      rip := entry.core.rip + 2
      flags := Ext.AluOp.flagsN .xor before before }, entry.memory⟩

private def afterTest (entry : MState) : MState :=
  ⟨{ (afterXor entry).core with
      rip := entry.core.rip + 5
      flags := Ext.logicFlagsN (pointer entry) }, entry.memory⟩

private def afterBranch (entry : MState) : MState :=
  ⟨{ (afterTest entry).core with rip := entry.core.rip + branchOffset (nextLabel entry) }, entry.memory⟩

private def readOperand : Ext.Mem := ⟨.reg .rdi, none, 0x18, fun _ => rfl⟩

private theorem stepXor {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code) :
    Open.step entry = some (afterXor entry) := by
  refine Open.step_of_listed (o := 0) (l := 2) (i := .base (.alu .d .xor (.reg .rax) .rax))
    loaded (by simp) (by decide) (by decide +kernel) ?_
  change Ext.exec (.alu .d .xor (.reg .rax) .rax) entry.core entry.memory = _
  rw [Ext.exec_alu_reg entry.core entry.memory .d .xor .rax .rax (by decide)]
  simp only [Ext.AluOp.resultN, BitVec.xor_self]
  rfl

private theorem stepTest {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code) :
    Open.step (afterXor entry) = some (afterTest entry) := by
  refine Open.step_of_listed (o := 2) (l := 3) (i := .base (.test .q (.reg .rdi) .rdi))
    loaded rfl (by decide) (by decide +kernel) ?_
  change Ext.exec (.test .q (.reg .rdi) .rdi) (afterXor entry).core entry.memory = _
  have mask : Ext.Sz.q.read (afterXor entry).core .rdi &&& Ext.Sz.q.read (afterXor entry).core .rdi =
      Ext.Sz.q.read (afterXor entry).core .rdi := BitVec.and_self
  rw [Ext.exec_test_reg, mask, Ext.Sz.read_q]
  have len : (Ext.Instr.test .q (.reg .rdi) .rdi).length = 3 := by decide
  rw [len]
  have reg : (afterXor entry).core.read .rdi = pointer entry := by
    simp [afterXor, pointer]
  rw [reg]
  simp [afterXor, BitVec.add_assoc]

private theorem stepBranch {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code) :
    Open.step (afterTest entry) = some (afterBranch entry) := by
  refine Open.step_of_listed (o := 5) (l := 2) (i := .base (.jcc8 .e 3))
    loaded rfl (by decide) (by decide +kernel) ?_
  change Ext.exec (.jcc8 .e 3) (afterTest entry).core entry.memory = _
  have flags : Ext.Cond.e.eval (afterTest entry).core.flags = some (decide (pointer entry = 0)) := by
    rfl
  rw [Ext.exec_jcc8 _ _ .e 3 _ flags]
  have len : (Ext.Instr.jcc8 .e 3).length = 2 := by decide
  rw [len]
  by_cases h : pointer entry = 0#64 <;>
    simp [afterTest, nextLabel, branchOffset, h, BitVec.add_assoc]

private theorem cfg_destination (entry : MState) :
    graph.entry.exec (model entry.memory) (fun label _ _ => some label) (entryStore entry) =
      some (nextLabel entry) := by
  by_cases h : pointer entry = 0#64 <;>
    simp [graph, CFG.Body.exec, CFG.Term.exec, model, Op.eval, Val.eval, entryStore,
      nextLabel, upd, h]

/-- The actual three decoded instructions reach the same successor selected
by the CFG entry block. Offsets are relative to the admitted code base. -/
theorem branch_agrees {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code) :
    ∃ target branch,
      graph.entry.exec (model entry.memory) (fun label _ _ => some label) (entryStore entry) = some target ∧
      run Open.step 3 entry = some branch ∧
      branch.core.rip = entry.core.rip + branchOffset target ∧
      branch.core.read .rdi = pointer entry ∧ branch.core.read .rax = 0 ∧ branch.memory = entry.memory := by
  refine ⟨nextLabel entry, afterBranch entry, cfg_destination entry, ?_, rfl, ?_, ?_, rfl⟩
  · simp [run, stepXor loaded, stepTest loaded, stepBranch loaded]
  · simp [afterBranch, afterTest, afterXor, pointer]
  · simp [afterBranch, afterTest, afterXor]

private def afterLoad (entry : MState) (value : Word) : MState :=
  ⟨{ (afterBranch entry).core.write .rax (zeroExtendLength value) with rip := entry.core.rip + 10 },
    entry.memory⟩

private theorem stepLoad {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (nonnull : pointer entry ≠ 0#64) {value : Word} (read : field entry.memory (pointer entry) = some value) :
    Open.step (afterBranch entry) = some (afterLoad entry value) := by
  refine Open.step_of_listed (o := 7) (l := 3) (i := .base (.load .d .rax readOperand))
    loaded (by simp [afterBranch, nextLabel, branchOffset, nonnull]) (by decide) (by decide +kernel) ?_
  change Ext.exec (.load .d .rax readOperand) (afterBranch entry).core entry.memory = _
  rw [Ext.exec_load]
  have len : (Ext.Instr.load .d .rax readOperand).length = 3 := by decide
  rw [len]
  have addr (next : Word) : readOperand.addr (afterBranch entry).core next = pointer entry + 0x18 := by
    simp [Ext.Mem.addr, readOperand, afterBranch, afterTest, afterXor, pointer]
  simp only [addr, Ext.Sz.bytes]
  change (match field entry.memory (pointer entry) with
    | some v => Ext.Result.ok _ _
    | none => Ext.Result.dataFault) = _
  rw [read]
  simp [afterBranch, nextLabel, branchOffset, nonnull, Ext.Sz.write,
    zeroExtendLength, BitVec.add_assoc]

private theorem cfg_null {entry : MState} (null : pointer entry = 0#64) :
    obs <$> graph.run (model entry.memory) (entryStore entry) = some (.ret, 0) := by
  simp [CFG.run, graph, CFG.Body.exec, CFG.Term.exec, CFG.jump, model, Op.eval, Val.eval,
    entryStore, upd, obs, null]

private theorem cfg_load {entry : MState} (nonnull : pointer entry ≠ 0#64) {value : Word}
    (read : field entry.memory (pointer entry) = some value) :
    obs <$> graph.run (model entry.memory) (entryStore entry) = some (.ret, zeroExtendLength value) := by
  simp [CFG.run, graph, CFG.Body.exec, CFG.Term.exec, CFG.jump, model, Op.eval, Val.eval,
    entryStore, upd, obs, nonnull, read]

private theorem notReturned {entry state : MState} (rsp : state.core.read .rsp = entry.core.read .rsp) :
    ¬ FnContract.Returned Open.isa entry state := by
  intro returned
  have stack := returned.2
  change state.core.read .rsp = entry.core.read .rsp + 8#64 at stack
  rw [rsp] at stack
  have absurd : (0 : Word) = 8 := by
    simpa using congrArg (fun sp => sp - entry.core.read .rsp) stack
  contradiction

private theorem prefixRuns {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code) :
    FnContract.RunsIn Open.isa (fun state => ¬ FnContract.Returned Open.isa entry state)
      entry (afterBranch entry) :=
  .step (notReturned rfl) (stepXor loaded)
    (.step (notReturned (by simp [afterXor])) (stepTest loaded)
      (.step (notReturned (by simp [afterTest, afterXor])) (stepBranch loaded) (.refl _)))

private theorem finish {entry preRet : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (pc : preRet.core.rip = entry.core.rip + 10)
    (rsp : preRet.core.read .rsp = entry.core.read .rsp) (memory : preRet.memory = entry.memory) :
    ∃ final, Open.step preRet = some final ∧ FnContract.Returned Open.isa entry final ∧
      final.core.read .rax = preRet.core.read .rax ∧ final.memory = entry.memory := by
  let returnPC := FnContract.retOf entry.core entry.memory
  let final : MState := ⟨{ preRet.core.write .rsp (entry.core.read .rsp + 8) with rip := returnPC }, entry.memory⟩
  refine ⟨final, ?_, ⟨rfl, by simp [final]⟩, by simp [final], rfl⟩
  refine Open.step_of_listed (o := 10) (l := 1) (i := .base .ret)
    (by rw [memory]; exact loaded) pc (by decide) (by decide +kernel) ?_
  have readable : preRet.memory.readBytes (preRet.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [returnPC]) := by
    rw [rsp, memory]
    exact saved
  change Ext.exec .ret preRet.core preRet.memory = _
  rw [Ext.exec_ret]
  simp only [Insn.exec, popWord_of_readBytes readable]
  rw [rsp, memory]
  rfl

theorem bridge_exists {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (ready : DataReady entry) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final := by
  have branchRun : run Open.step 3 entry = some (afterBranch entry) := by
    simp [run, stepXor loaded, stepTest loaded, stepBranch loaded]
  have readyRet : ∃ preRet,
      FnContract.RunsIn Open.isa (fun state => ¬ FnContract.Returned Open.isa entry state)
        (afterBranch entry) preRet ∧
      ((nextLabel entry = .ret ∧ preRet = afterBranch entry) ∨
        (nextLabel entry = .load ∧ Open.step (afterBranch entry) = some preRet)) ∧
      preRet.core.rip = entry.core.rip + 10 ∧ preRet.core.read .rsp = entry.core.read .rsp ∧
      preRet.memory = entry.memory ∧
      (obs <$> graph.run (model entry.memory) (entryStore entry)) = some (.ret, preRet.core.read .rax) := by
    by_cases null : pointer entry = 0#64
    · refine ⟨afterBranch entry, .refl _, .inl ⟨?_, rfl⟩, ?_, ?_, rfl, ?_⟩
      · simp [nextLabel, null]
      · simp [afterBranch, nextLabel, branchOffset, null]
      · simp [afterBranch, afterTest, afterXor]
      · simpa [afterBranch, afterTest, afterXor] using cfg_null null
    · obtain ⟨value, read⟩ := ready null
      have step := stepLoad loaded null read
      refine ⟨afterLoad entry value, .step (notReturned ?_) step (.refl _), .inr ⟨?_, step⟩,
        rfl, ?_, rfl, ?_⟩
      · simp [afterBranch, afterTest, afterXor]
      · simp [nextLabel, null]
      · simp [afterLoad, afterBranch, afterTest, afterXor]
      · simpa [afterLoad] using cfg_load null read
  obtain ⟨preRet, tailSteps, arm, pc, rsp, memory, value⟩ := readyRet
  obtain ⟨final, step, returned, result, frame⟩ := finish loaded saved pc rsp memory
  refine ⟨final, ⟨?_, returned⟩, nextLabel entry, afterBranch entry, preRet,
    cfg_destination entry, branchRun, rfl, arm, pc, step, ?_, frame⟩
  · exact FnContract.runsIn_trans (prefixRuns loaded)
      (FnContract.runsIn_trans tailSteps (.step (notReturned rsp) step (.refl _)))
  · rwa [result]

theorem bridge_of_firstReturn {entry final : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (ready : DataReady entry) (actual : FnContract.FirstReturn Open.isa entry final) :
    Bridge entry final := by
  obtain ⟨witness, first, bridge⟩ := bridge_exists loaded saved ready
  exact (FnContract.firstReturn_unique first actual) ▸ bridge

private def stackBytes : List Byte := Silmaril.Machine.LittleEndian.encodeWords [0x9000]
private def lengthBytes : List Byte := [0x78, 0x56, 0x34, 0x12]
private def stackBacking : Silmaril.Process.ByteMemory := Memory.install ∅ 0x8008 stackBytes

private def fieldBytes (hasField : Bool) : List Byte := if hasField then lengthBytes else []

private def fieldBacking (hasField : Bool) : Silmaril.Process.ByteMemory :=
  Memory.install stackBacking 0x4018 (fieldBytes hasField)

private def fixtureMemory (hasField : Bool) : Memory :=
  ⟨[⟨0x10060, code.length, ⟨false, false, true⟩⟩, ⟨0x8008, 8, ⟨true, false, false⟩⟩] ++
      (if hasField then [⟨0x4018, 4, ⟨true, false, false⟩⟩] else []),
    Memory.install (fieldBacking hasField) 0x10060 code⟩

private def fixture (ptr : Word) (hasField : Bool) : MState :=
  ⟨{ regs := fun r => if r = .rsp then 0x8008 else if r = .rdi then ptr else 0xfeed,
     rip := 0x10060, flags := ⟨none, none, none, none, none, none⟩ }, fixtureMemory hasField⟩

private theorem fixture_code (ptr : Word) (hasField : Bool) :
    Ext.Loaded (fixture ptr hasField).memory (fixture ptr hasField).core.rip code := by
  have permitted : (fixtureMemory hasField).Permitted .execute 0x10060 code.length := by
    cases hasField <;> decide
  exact Memory.readWith_eq _ _ _ _ permitted (fun i hi => Memory.install_get _ _ _ i hi)

private theorem fixture_stack (hasField : Bool) : (fixtureMemory hasField).readBytes 0x8008 8 = some stackBytes := by
  have permitted : (fixtureMemory hasField).Permitted .read 0x8008 stackBytes.length := by
    cases hasField <;> decide
  change (fixtureMemory hasField).readWith .read 0x8008 stackBytes.length = some stackBytes
  refine Memory.readWith_eq _ _ _ _ permitted (fun i hi => ?_)
  have upper : i < 8 := hi
  have below : 0x8008 + i < 0x10060 := by omega
  have above : 0x4018 + (fieldBytes hasField).length ≤ 0x8008 + i := by
    cases hasField <;> simp [fieldBytes, lengthBytes] <;> omega
  change (Memory.install (fieldBacking hasField) 0x10060 code).get? (0x8008 + i) = _
  rw [Memory.install_outside _ _ _ _ (.inl below)]
  change (Memory.install stackBacking 0x4018 (fieldBytes hasField)).get? (0x8008 + i) = _
  rw [Memory.install_outside _ _ _ _ (.inr above)]
  exact Memory.install_get _ _ _ _ hi

private theorem fixture_returnSlot (ptr : Word) (hasField : Bool) : ReturnSlot (fixture ptr hasField) := by
  have ret : FnContract.retOf (fixture ptr hasField).core (fixtureMemory hasField) = 0x9000 := by
    change (((fixtureMemory hasField).readBytes 0x8008 8).bind wordOfBytes?).getD 0 = 0x9000
    rw [fixture_stack]
    rfl
  change (fixtureMemory hasField).readBytes 0x8008 8 = some (Silmaril.Machine.LittleEndian.encodeWords
    [FnContract.retOf (fixture ptr hasField).core (fixtureMemory hasField)])
  rw [ret]
  exact fixture_stack hasField

private theorem fixture_field_read : (fixtureMemory true).readBytes 0x4018 4 = some lengthBytes := by
  change (fixtureMemory true).readWith .read 0x4018 lengthBytes.length = some lengthBytes
  refine Memory.readWith_eq _ _ _ _ (by decide) (fun i hi => ?_)
  have upper : i < 4 := hi
  have below : 0x4018 + i < 0x10060 := by omega
  change (Memory.install (fieldBacking true) 0x10060 code).get? (0x4018 + i) = _
  rw [Memory.install_outside _ _ _ _ (.inl below)]
  exact Memory.install_get _ _ _ _ hi

private theorem null_no_field : field (fixtureMemory false) 0 = none := by
  have denied : (fixtureMemory false).checkSpan .read 0x18 4 = false := by decide
  change ((fixtureMemory false).readBytes 0x18 4).map (fun bs => BitVec.ofNat 64 (Ext.leValue bs)) = none
  simp [Memory.readBytes, Memory.readWith, denied]

private theorem readyField : field (fixtureMemory true) 0x4000 = some 0x12345678 := by
  unfold field Ext.loadN
  change ((fixtureMemory true).readBytes 0x4018 4).map (fun bs => BitVec.ofNat 64 (Ext.leValue bs)) = _
  rw [fixture_field_read]
  rfl

private theorem null_returns :
    ∃ final, FnContract.FirstReturn Open.isa (fixture 0 false) final ∧
      Bridge (fixture 0 false) final ∧ final.core.read .rax = 0 := by
  have null : pointer (fixture 0 false) = 0#64 := rfl
  have ready : DataReady (fixture 0 false) := fun notNull => (notNull null).elim
  obtain ⟨final, first, bridge⟩ := bridge_exists (fixture_code 0 false) (fixture_returnSlot 0 false) ready
  have details := bridge
  obtain ⟨_, _, _, _, _, _, _, _, _, result, _⟩ := details
  have equals := Option.some.inj ((cfg_null null).symm.trans result)
  exact ⟨final, first, bridge, (congrArg Prod.snd equals).symm⟩

private theorem bounded_returns :
    ∃ final, FnContract.FirstReturn Open.isa (fixture 0x4000 true) final ∧
      Bridge (fixture 0x4000 true) final ∧ final.core.read .rax = 0x12345678 := by
  have nonnull : pointer (fixture 0x4000 true) ≠ 0#64 := by decide
  have ready : DataReady (fixture 0x4000 true) := fun _ => ⟨_, readyField⟩
  obtain ⟨final, first, bridge⟩ := bridge_exists (fixture_code 0x4000 true) (fixture_returnSlot 0x4000 true) ready
  have details := bridge
  obtain ⟨_, _, _, _, _, _, _, _, _, result, _⟩ := details
  have equals := Option.some.inj ((cfg_load nonnull readyField).symm.trans result)
  exact ⟨final, first, bridge, (congrArg Prod.snd equals).symm⟩

private theorem rejected_load : ¬ DataReady (fixture 0x4000 false) := by
  have denied : (fixtureMemory false).checkSpan .read 0x4018 4 = false := by decide
  have missing : field (fixtureMemory false) 0x4000 = none := by
    change ((fixtureMemory false).readBytes 0x4018 4).map (fun bs => BitVec.ofNat 64 (Ext.leValue bs)) = none
    simp [Memory.readBytes, Memory.readWith, denied]
  intro ready
  obtain ⟨_, read⟩ := ready (by decide)
  change field (fixtureMemory false) 0x4000 = _ at read
  rw [missing] at read
  contradiction

/-- The rule admits the null arm in a state without readable pointee bytes. -/
theorem null_witness :
    ∃ entry final, pointer entry = 0 ∧ field entry.memory 0 = none ∧
      Ext.Loaded entry.memory entry.core.rip code ∧ ReturnSlot entry ∧
      FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final ∧ final.core.read .rax = 0 := by
  obtain ⟨final, first, matched, value⟩ := null_returns
  exact ⟨fixture 0 false, final, rfl, null_no_field, fixture_code 0 false,
    fixture_returnSlot 0 false, first, matched, value⟩

/-- The rule admits a bounded non-null field containing four concrete bytes. -/
theorem bounded_witness :
    ∃ entry final, pointer entry = 0x4000 ∧ (pointer entry).toNat + 28 ≤ addressLimit ∧
      field entry.memory (pointer entry) = some 0x12345678 ∧
      Ext.Loaded entry.memory entry.core.rip code ∧ ReturnSlot entry ∧
      FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final ∧ final.core.read .rax = 0x12345678 := by
  obtain ⟨final, first, matched, value⟩ := bounded_returns
  exact ⟨fixture 0x4000 true, final, rfl, by decide, readyField, fixture_code 0x4000 true,
    fixture_returnSlot 0x4000 true, first, matched, value⟩

end Silmaril.Proofs.Machine.Region.X86.SqliteStrLength
