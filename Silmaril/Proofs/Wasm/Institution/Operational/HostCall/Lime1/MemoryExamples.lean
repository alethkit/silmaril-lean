module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Lime1Context.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryExamples

open Execution.Runtime (Frame MemInst ModuleInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (Declaration)
open CallContinuation.OuterCall.Ranked

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def arg : Wasm.V1.MemArg := Graph.Memory32.immediate 1
private abbrev word : BitVec 32 := 0x04030201

private def zero : ByteArray := ⟨#[0, 0, 0, 0, 0, 0]⟩
private def before : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩
private def written : ByteArray := ⟨#[0xaa, 1, 2, 3, 4, 0xbb]⟩
private def initial : MemInst := ⟨zero, some 1⟩
private def signature : Wasm.Lime1.FuncType := ⟨[.int .i32], [.int .i64, .int .i32]⟩
private def hostType : Wasm.Lime1.FuncType := ⟨[.int .i32, .int .i64, .int .i32], [.int .i32]⟩
private def calleeModule : ModuleInst := { types := [signature], memories := [⟨1⟩] }
private def caller : Frame := ⟨[i64 111], { types := [signature], tables := [⟨0⟩], memories := [⟨1⟩] }⟩
private def callee (ptr : BitVec 32) : Frame := ⟨[i32 ptr], calleeModule⟩
private def callerSaved : List Value := [i32 23]
private def tail : List Admin := [.invoke ⟨1⟩]

private def fn : Graph.Memory32.Function where
  declaration := (⟨calleeModule, ⟨0⟩, signature.params, [], signature.results⟩ : Declaration)
  rank := 0
  initial := [i64 9, i32 0, i32 word]
  code := [.store 1, .ranked (.numeric (.get ⟨0⟩)), .load 1]

private def writeThenLoad : Wasm.Lime1.Func := fn.v1Func.toLime

-- Reuse the V1 graph's operator typing with Lime1's ordered result list.
example : fn.WellTyped fn.initial fn.code := by unfold Graph.Memory32.Function.WellTyped; decide
example : ¬ fn.WellTyped [i64 9, i64 0, i32 word] fn.code := by unfold Graph.Memory32.Function.WellTyped; decide

private def base : Store Nat :=
  { memories := [⟨⟨#[0xcc]⟩, none⟩, initial], tables := [⟨[some ⟨0⟩], none⟩],
    funcs := [.wasm signature calleeModule writeThenLoad, .host hostType 7] }

private def mem : Memory32 base := ⟨⟨1⟩, initial, rfl⟩
private def host : HostSemantics Nat := fun code store operands outcome =>
  code = 7 ∧ store = mem.store written ∧ operands = [i32 23, i64 9, i32 word] ∧
    outcome = .returned (mem.store written) (.values [i32 42])

private def launch (ptr : BitVec 32) : Config Nat :=
  ⟨mem.store before, caller, values (callerSaved ++ [i32 ptr, i32 0]) ++ [.source (.callIndirect ⟨0⟩)] ++ tail⟩

private def inCallee (ptr : BitVec 32) (bytes : ByteArray) (body : List Admin) : Config Nat :=
  ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode
    signature.results.length (callee ptr) callerSaved tail body⟩

private theorem atStore (ptr : BitVec 32) :
    Steps host (launch ptr) (inCallee ptr before (expression writeThenLoad.body)) := by
  have resolve : Step host (launch ptr)
      ⟨mem.store before, caller, values (callerSaved ++ [i32 ptr]) ++ [.invoke ⟨0⟩] ++ tail⟩ :=
    .context (.callIndirect _ _ ⟨0⟩ 0 _ ⟨0⟩ (.wasm signature calleeModule writeThenLoad)
      signature rfl rfl rfl rfl rfl) (callerSaved ++ [i32 ptr]) tail
  exact (Relation.ReflTransGen.single resolve).tail
    (.context (.invokeWasm _ caller ⟨0⟩ signature calleeModule writeThenLoad [i32 ptr] rfl rfl) callerSaved tail)

private def loadTail : List Admin := [.source (.localGet ⟨0⟩), .source (.intLoad .i32 none arg)]

private theorem writeStep (ptr : BitVec 32) :
    Step host (inCallee ptr before (expression writeThenLoad.body))
      (inCallee ptr written (values [i64 9] ++ loadTail)) := by
  have edge : MemoryWrite.EdgeAt before 1 (.store 0 word) (.written written) :=
    MemoryWrite.fact_at (.write 0 word written (by decide))
  exact (mem.activation_store_iff_at (bytes := before) (callee := callee ptr) (arg := arg) (ptr := 0) (word := word) (saved := [i64 9])
    (tail := loadTail) rfl rfl).mpr (.inl ⟨written, edge, rfl, rfl⟩)

private theorem atLoad (ptr : BitVec 32) :
    Steps host (launch ptr) (inCallee ptr written (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load ptr))) :=
  ((atStore ptr).tail (writeStep ptr)).tail
    (.context (.frame (.label (.context (.localGet _ _ ⟨0⟩ (i32 ptr) rfl)
      [i64 9] [.source (.intLoad .i32 none arg)]) 2 []) 2 caller) callerSaved tail)

-- The first native prefix observes the callee's write before it loads a result.
example : Steps host (launch 0) (inCallee 0 written (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load 0))) :=
  atLoad 0

example : Steps host (launch 0) ⟨mem.store written, caller, values [i32 42]⟩ := by
  have writtenPrefix := atLoad 0
  have loaded : Step host (inCallee 0 written (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load 0)))
      (inCallee 0 written (values [i64 9, i32 word])) :=
    (MemoryWrite.lime_activation_load_step_iff_at (immediate := arg) (ptr := 0) (saved := [i64 9]) (tail := [])
      (mem.frameMemory_store (bytes := written) (active := callee 0) rfl)).mpr
      ⟨.value word, MemoryQuery.fact_at (.load 0 word (by decide)), rfl⟩
  have labelExited : Step host (inCallee 0 written (values [i64 9, i32 word]))
      ⟨mem.store written, caller, values callerSaved ++ [.frame 2 (callee 0) (values [i64 9, i32 word])] ++ tail⟩ :=
    .context (.frame (.pure _ _ (.labelDone 2 [] [i64 9, i32 word])) 2 caller) callerSaved tail
  have calleeExited : Step host
      ⟨mem.store written, caller, values callerSaved ++ [.frame 2 (callee 0) (values [i64 9, i32 word])] ++ tail⟩
      ⟨mem.store written, caller, values [i32 23, i64 9, i32 word] ++ tail⟩ :=
    .context (.pure _ _ (.frameDone 2 (callee 0) [i64 9, i32 word] rfl)) callerSaved tail
  have observed : Step host ⟨mem.store written, caller, values [i32 23, i64 9, i32 word] ++ tail⟩
      ⟨mem.store written, caller, values [i32 42]⟩ :=
    .invokeHost _ _ caller ⟨1⟩ hostType 7 [i32 23, i64 9, i32 word] (.values [i32 42])
      rfl rfl ⟨rfl, rfl, rfl, rfl⟩
  exact (((writtenPrefix.tail loaded).tail labelExited).tail calleeExited).tail observed

example : Steps host (launch (-1)) ⟨mem.store written, caller, [.trap]⟩ := by
  have writtenPrefix := atLoad (-1)
  have bounds : Step host (inCallee (-1) written (values [i64 9] ++ MemoryQuery.limeCodeAt arg (.load (-1))))
      (inCallee (-1) written (values [i64 9] ++ [.trap])) :=
    (MemoryWrite.lime_activation_load_step_iff_at (immediate := arg) (ptr := -1) (saved := [i64 9]) (tail := [])
      (mem.frameMemory_store (bytes := written) (active := callee (-1)) rfl)).mpr
      ⟨.trap, MemoryQuery.load_trap_iff_at.mpr (by decide), rfl⟩
  have erased : Step host (inCallee (-1) written (values [i64 9] ++ [.trap])) (inCallee (-1) written [.trap]) :=
    .context (.frame (.label (.pure _ _ (.trapValues (i64 9) [] [])) 2 []) 2 caller) callerSaved tail
  have labelExited : Step host (inCallee (-1) written [.trap])
      ⟨mem.store written, caller, values callerSaved ++ [.frame 2 (callee (-1)) [.trap]] ++ tail⟩ :=
    .context (.frame (.pure _ _ (.labelTrap 2 [])) 2 caller) callerSaved tail
  have calleeExited : Step host ⟨mem.store written, caller, values callerSaved ++ [.frame 2 (callee (-1)) [.trap]] ++ tail⟩
      ⟨mem.store written, caller, values callerSaved ++ [.trap] ++ tail⟩ :=
    .context (.pure _ _ (.frameTrap 2 (callee (-1)))) callerSaved tail
  exact ((((writtenPrefix.tail bounds).tail erased).tail labelExited).tail calleeExited).tail
    (.pure _ _ (.trapValues (i32 23) [] tail))

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryExamples
