module

import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame FuncAddr Value)
open Silmaril.Wasm.Institution.Operational
open CallContinuation.Nested
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private def addr : FuncAddr := ⟨0⟩
private def caller : Frame := ⟨[.int .i64 9], {}⟩
private def outer : Frame := ⟨[.int .i32 17], { funcs := [addr] }⟩
private def arg : Value := .int .i64 18
private def result : Value := .int .i32 42
private def fn : CallFrame.Callee :=
  ⟨{}, ⟨0⟩, [.int .i64], [.int .i32], some (.int .i32), .ret [.int .i64 81, result]⟩
private def failing : CallFrame.Callee := { fn with program := .unreachable }

private def store (callee : CallFrame.Callee) : V1.Execution.Store Unit :=
  { funcs := [.wasm callee.type callee.module callee.v1Func] }

private theorem allocated (callee : CallFrame.Callee) :
    (store callee).funcs[addr.value]? = some (.wasm callee.type callee.module callee.v1Func) := rfl

private def start : State := .label (.active (.invoke [] [arg]))
private def returned : State := .done (.values [result])

private theorem entry (callee : CallFrame.Callee) (params : callee.params = [.int .i64]) :
    Edge callee 1 start (.label (.active (.label [] (callee.init [arg]) (.code callee.program)))) :=
  underLabel (CallContinuation.call (by trivial) (CallFrame.fact (.enter [] [arg] (by rw [params]; rfl))))

private theorem returnPath : Runs fn 1 start returned := by
  have stage₁ := Relation.ReflTransGen.single (entry fn rfl)
  have stage₂ := stage₁.tail (underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.labelReturn [] (fn.init [arg]) [.int .i64 81, result]))))
  have stage₃ := stage₂.tail (underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.frameReturn [] (fn.init [arg]) [.int .i64 81] [result] rfl))))
  exact ((stage₃.tail (underLabel (CallContinuation.fact (.resume [result])))).tail
    (fact (.labelValues [result]))).tail (fact (.frameValues [result] rfl))

private theorem trapPath : Runs failing 1 start (.done .trap) := by
  have stage₁ := Relation.ReflTransGen.single (entry failing rfl)
  have stage₂ := stage₁.tail (underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.unreachable [] (failing.init [arg])))))
  have stage₃ := stage₂.tail (underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.labelTrap [] (failing.init [arg])))))
  have stage₄ := stage₃.tail (underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.frameTrap [] (failing.init [arg])))))
  exact ((stage₄.tail (underLabel (CallContinuation.fact (.discardTail [] [])))).tail
    (fact .labelTrap)).tail (fact .frameTrap)

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store fn) caller outer addr fn 1 start)
    ⟨store fn, caller, [.source (.intConst .i32 42)]⟩ :=
  (v1_run_iff (allocated fn) (show Admitted fn start from ⟨trivial, rfl, rfl⟩)).mpr
    ⟨returned, returnPath, trivial, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost (v1Config (store failing) caller outer addr failing 1 start).toLime
    ⟨(store failing).mapCode V1.Func.toLime, caller, [.trap]⟩ := by
  rw [v1_to_lime]
  exact (lime_run_iff (CallFrame.allocated_toLime (allocated failing))
    (show Admitted failing start from ⟨trivial, rfl, trivial⟩)).mpr
      ⟨.done .trap, trapPath, trivial, rfl⟩

example {target : Core.Config Unit}
    (h : Core.Steps Numerics.Profile.spec noHost
      (v1Config (store fn) caller outer addr fn 1 start).toLime.toCore target) :
    ∃ out, Runs fn 1 start out ∧ Admitted fn out ∧
      target = (v1Config (store fn) caller outer addr fn 1 out).toLime.toCore ∧ target.frame = caller.toCore := by
  have found := CallFrame.allocated_toLime (allocated fn)
  rw [v1_to_lime, lime_to_core caller outer found] at h
  have ready : Admitted fn start := ⟨trivial, rfl, rfl⟩
  obtain ⟨out, run, good, eq⟩ := (core_run_iff (CallFrame.allocated_toCore found) ready).mp h
  exact ⟨out, run, good, by rw [v1_to_lime, lime_to_core caller outer found, eq], congrArg Core.Config.frame eq⟩

example : V1.Execution.Step CallFrame.v1NoHost
    ⟨store fn, caller, [.frame 1 outer [.label 1 []
      [.source (.intConst .i64 18), .source (.call ⟨0⟩), .source .nop]]]⟩
    (v1Config (store fn) caller outer addr fn 1 start) :=
  .frame (.label (.context (.call (store fn) outer ⟨0⟩ addr rfl) [arg] [.source .nop]) 1 []) 1 caller
