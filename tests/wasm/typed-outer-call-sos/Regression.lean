module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value FuncAddr)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private def x : Value := .int .i64 12
private def output : Value := .int .i32 19
private def fn : CallFrame.Callee :=
  ⟨{}, ⟨0⟩, [.int .i64], [.int .i32], some (.int .i32), .ret [.int .i64 73, output]⟩
private def trapFn : CallFrame.Callee := { fn with program := .unreachable }
private def caller : Frame := ⟨[.int .i32 51], { funcs := [⟨0⟩] }⟩

private def site (inner : CallFrame.Callee) : CallSite :=
  ⟨⟨0⟩, ⟨0⟩, ⟨1⟩, [.int .i32 8],
    ⟨{ funcs := [⟨1⟩] }, ⟨0⟩, [.int .i32], [.int .i64], ⟨0⟩, [x], inner⟩⟩

private def store (inner : CallFrame.Callee) : V1.Execution.Store Unit :=
  { funcs := [.wasm (site inner).callee.type (site inner).callee.moduleInst (v1Func (site inner).callee),
    .wasm inner.type inner.module inner.v1Func] }

private theorem ready (inner : CallFrame.Callee) (arg : inner.params = [.int .i64])
    (body : inner.program.Typed inner) : V1Guard (store inner) caller (site inner) :=
  ⟨⟨rfl, arg.symm, body, by change (⟨0⟩ : FuncAddr) ≠ ⟨1⟩; decide⟩, rfl, rfl, rfl, rfl⟩

private theorem stem (callee : CallFrame.Callee) :
    Runs (site callee) .call (.nested (site callee).start) :=
  ((Relation.ReflTransGen.single (fact .resolve)).tail (fact .enter)).tail
    (fact .resolveInner)

private theorem returnPath :
    Runs (site fn) .call (.nested (.done (.values [output]))) := by
  let stack := fn.init [x]
  have one := (stem fn).tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.enter [] [x] rfl)))))
  have two := one.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.labelReturn [] stack [.int .i64 73, output])))))
  have three := two.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.frameReturn [] stack [.int .i64 73] [output] rfl)))))
  have four := three.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.fact (.resume [output]))))
  exact (four.tail (delegate (CallContinuation.Nested.fact (.labelValues [output])))).tail
    (delegate (CallContinuation.Nested.fact (.frameValues [output] rfl)))

private theorem trapPath :
    Runs (site trapFn) .call (.nested (.done .trap)) := by
  let stack := trapFn.init [x]
  have one := (stem trapFn).tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.enter [] [x] rfl)))))
  have two := one.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.unreachable [] stack)))))
  have three := two.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.labelTrap [] stack)))))
  have four := three.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call (by trivial)
    (CallFrame.fact (.frameTrap [] stack)))))
  have five := four.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.fact (.discardTail [] []))))
  exact (five.tail (delegate (CallContinuation.Nested.fact .labelTrap))).tail (delegate (CallContinuation.Nested.fact .frameTrap))

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store fn) caller (site fn) .call)
    ⟨store fn, caller, [.source (.intConst .i32 19)]⟩ := by
  apply (v1_run_iff (ready fn rfl rfl) (a := .call) trivial).mpr
  exact ⟨.nested (.done (.values [output])), returnPath, trivial, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (v1Config (store trapFn) caller (site trapFn) .call).toLime
    ⟨(store trapFn).mapCode V1.Func.toLime, caller, [.trap]⟩ := by
  rw [v1_to_lime]
  apply (lime_run_iff (guard_to_lime (ready trapFn rfl trivial)) (a := .call) trivial).mpr
  exact ⟨.nested (.done .trap), trapPath, trivial, rfl⟩

example {target : Core.Config Unit}
    (run : Core.Steps Profile.spec noHost (v1Config (store fn) caller (site fn) .call).toLime.toCore target) :
    ∃ out, Runs (site fn) .call out ∧
      target = (v1Config (store fn) caller (site fn) out).toLime.toCore := by
  have g := guard_to_lime (ready fn rfl rfl)
  rw [v1_to_lime, lime_to_core g] at run
  obtain ⟨out, path, _, eq⟩ := (core_run_iff (guard_to_core g) (a := .call) trivial).mp run
  exact ⟨out, path, by rw [v1_to_lime, lime_to_core g, eq]⟩

example : Core.Steps Profile.spec noHost (v1Config (store fn) caller (site fn) .call).toLime.toCore
    ⟨((store fn).mapCode V1.Func.toLime).toCore, caller.toCore, [.plain (.intConst .i32 19)]⟩ := by
  have g := guard_to_lime (ready fn rfl rfl)
  rw [v1_to_lime, lime_to_core g]
  exact (core_run_iff (guard_to_core g) (a := .call) trivial).mpr
    ⟨.nested (.done (.values [output])), returnPath, trivial, rfl⟩

example : Core.Steps Profile.spec noHost (v1Config (store trapFn) caller (site trapFn) .call).toLime.toCore
    ⟨((store trapFn).mapCode V1.Func.toLime).toCore, caller.toCore, [.trap]⟩ := by
  have g := guard_to_lime (ready trapFn rfl trivial)
  rw [v1_to_lime, lime_to_core g]
  exact (core_run_iff (guard_to_core g) (a := .call) trivial).mpr
    ⟨.nested (.done .trap), trapPath, trivial, rfl⟩

example : V1.Execution.Step CallFrame.v1NoHost (v1Config (store fn) caller (site fn) .invoke)
    ⟨store fn, caller, [.frame 1 ⟨[.int .i32 8, .int .i64 0], { funcs := [⟨1⟩] }⟩
      [.label 1 [] [.source (.intConst .i64 12), .source (.call ⟨0⟩), .source .nop]]]⟩ :=
  (v1_step_iff (ready fn rfl rfl) (a := .invoke) trivial).mpr ⟨.entered, fact .enter, rfl⟩

example {target : Core.Config Unit}
    (run : Core.Steps Profile.spec noHost
      (v1Config (store trapFn) caller (site trapFn) .call).toLime.toCore target) :
    ∃ out, Runs (site trapFn) .call out ∧
      target = (v1Config (store trapFn) caller (site trapFn) out).toLime.toCore := by
  have guard := guard_to_lime (ready trapFn rfl trivial)
  rw [v1_to_lime, lime_to_core guard] at run
  obtain ⟨out, path, _, eq⟩ := (core_run_iff (guard_to_core guard) (a := .call) trivial).mp run
  exact ⟨out, path, by rw [v1_to_lime, lime_to_core guard, eq]⟩
