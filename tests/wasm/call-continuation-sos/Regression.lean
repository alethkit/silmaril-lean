module

import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame FuncAddr Value)
open Silmaril.Wasm.Institution.Operational
open CallContinuation
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private def addr : FuncAddr := ⟨0⟩
private def caller : Frame := ⟨[.int .i64 51], {}⟩
private def kept : List Value := [.int .i64 13, .int .i32 17]
private def result : Value := .int .i32 42
private def fn : CallFrame.Callee := ⟨{}, ⟨0⟩, [], [], some (.int .i32), .ret [.int .i64 31, result]⟩
private def failing : CallFrame.Callee := { fn with program := .unreachable }

private def store (callee : CallFrame.Callee) : V1.Execution.Store Unit :=
  { funcs := [.wasm callee.type callee.module callee.v1Func] }

private theorem allocated (callee : CallFrame.Callee) :
    (store callee).funcs[addr.value]? = some (.wasm callee.type callee.module callee.v1Func) := rfl

private theorem returnStep :
    Edge fn (.active (.exit kept [] (.ret [.int .i64 31, result]))) (.resume (kept ++ [result])) :=
  call (by trivial) (CallFrame.fact (.frameReturn kept [] [.int .i64 31] [result] rfl))

example : V1.Execution.Step CallFrame.v1NoHost
    (v1Config (store fn) caller addr fn (.active (.exit kept [] (.ret [.int .i64 31, result]))))
    ⟨store fn, caller, [.source (.intConst .i64 13), .source (.intConst .i32 17),
      .source (.intConst .i32 42), .source .nop]⟩ :=
  v1_sound (allocated fn) returnStep

example : Lime1.Execution.Step CallFrame.limeNoHost
    (v1Config (store fn) caller addr fn (.resume (kept ++ [result]))).toLime
    (v1Config (store fn) caller addr fn (.done (kept ++ [result]))).toLime := by
  rw [v1_to_lime, v1_to_lime]
  exact lime_sound (CallFrame.allocated_toLime (allocated fn)) (fact (.resume _))

example : V1.Execution.Steps CallFrame.v1NoHost
    (v1Config (store failing) caller addr failing (.active (.exit kept [] .trap)))
    ⟨store failing, caller, [.trap]⟩ := by
  apply Relation.ReflTransGen.tail
  · exact .single (v1_sound (allocated failing) (call (by trivial) (CallFrame.fact (.frameTrap kept []))))
  · exact v1_sound (allocated failing) (fact (.discardTail [] kept))

example {target : Core.Config Unit}
    (h : Core.Steps Numerics.Profile.spec noHost
      (v1Config (store fn) caller addr fn (.active (.invoke kept []))).toLime.toCore target) :
    ∃ out, Runs fn (.active (.invoke kept [])) out ∧ Admitted fn out ∧
      target = (v1Config (store fn) caller addr fn out).toLime.toCore ∧ target.frame = caller.toCore := by
  have found := CallFrame.allocated_toLime (allocated fn)
  rw [v1_to_lime, lime_to_core caller found] at h
  have ready : Admitted fn (.active (.invoke kept [])) := ⟨trivial, rfl, rfl⟩
  obtain ⟨out, run, guard, eq⟩ := (core_run_iff (CallFrame.allocated_toCore found) ready).mp h
  exact ⟨out, run, guard, by rw [v1_to_lime, lime_to_core caller found, eq], congrArg Core.Config.frame eq⟩
