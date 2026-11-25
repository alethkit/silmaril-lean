module

import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Native.Thms
import Silmaril.Wasm.Execution.Core.Inversion.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallFrame
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev a : Runtime.FuncAddr := ⟨0⟩
private abbrev caller : Runtime.Frame := ⟨[.int .i32 900], { funcs := [a] }⟩
private abbrev calleeModule : Runtime.ModuleInst := { globals := [⟨7⟩] }
private abbrev saved : List Runtime.Value := [.int .i64 200, .int .i32 300]
private abbrev args : List Runtime.Value := [.int .i32 11, .int .i64 22]
private abbrev assigned : Runtime.Value := .int .i32 33
private abbrev result : Runtime.Value := .int .i64 22
private abbrev slot : LocalIdx := ⟨2⟩
private abbrev param : LocalIdx := ⟨1⟩

private def localFn : Callee :=
  ⟨calleeModule, ⟨0⟩, [.int .i32, .int .i64], [.int .i32], some (.int .i64),
    .locals [.value assigned, .set slot, .get param]⟩

private def store (fn : Callee) : V1.Execution.Store Unit :=
  { funcs := [.wasm fn.type fn.module fn.v1Func] }

private theorem allocated (fn : Callee) :
    (store fn).funcs[a.value]? = some (.wasm fn.type fn.module fn.v1Func) := rfl

private abbrev start : State := .invoke saved args
private abbrev done : State := .returned saved [result]
private abbrev newLocals : List Runtime.Value := args ++ [assigned]

private theorem ready : Admitted localFn start := ⟨rfl, rfl⟩
private theorem doneTyped : Admitted localFn done := rfl

private theorem write : Locals.Edge
    ⟨localFn.init args, [.value assigned, .set slot, .get param]⟩ ⟨newLocals, [.get param]⟩ :=
  Locals.context (Locals.fact (.set _ slot assigned (by decide))) [] [.get param]

private theorem readParam : Locals.Edge ⟨newLocals, [.get param]⟩ ⟨newLocals, [.value result]⟩ :=
  Locals.fact (.get _ param result rfl)

private theorem path : Runs localFn start done :=
  ((((Relation.ReflTransGen.single (fact (.enter saved args rfl))).tail (reduce saved write)).tail
    (reduce saved readParam)).tail (fact (.labelValues saved newLocals [result]))).tail
      (fact (.frameValues saved newLocals [result] rfl))

example : V1.Execution.Steps v1NoHost
    (v1Config (store localFn) caller a localFn start) (v1Config (store localFn) caller a localFn done) :=
  (v1_run_iff (allocated localFn) ready).mpr ⟨done, path, doneTyped, rfl⟩

example : Core.Steps Numerics.Profile.spec noHost
    (v1Config (store localFn) caller a localFn start).toLime.toCore
    (v1Config (store localFn) caller a localFn done).toLime.toCore := by
  have found := allocated_toLime (allocated localFn)
  rw [v1_to_lime, v1_to_lime, lime_to_core caller found, lime_to_core caller found]
  exact (core_run_iff (allocated_toCore found) ready).mpr ⟨done, path, doneTyped, rfl⟩

-- Expected order is caller values, then the result, in the unchanged caller.
example : (v1Config (store localFn) caller a localFn done).frame = caller ∧
    (v1Config (store localFn) caller a localFn done).code =
      V1.Execution.values [.int .i64 200, .int .i32 300, .int .i64 22] := ⟨rfl, rfl⟩

example : localFn.init args = [.int .i32 11, .int .i64 22, .int .i32 0] := rfl

example {target : Core.Config Unit}
    (h : Core.Steps Numerics.Profile.spec noHost
      (v1Config (store localFn) caller a localFn start).toLime.toCore target) :
    ∃ out, Runs localFn start out ∧ Admitted localFn out ∧
      target = (v1Config (store localFn) caller a localFn out).toLime.toCore ∧
      target.frame = caller.toCore := by
  have found := allocated_toLime (allocated localFn)
  rw [v1_to_lime, lime_to_core caller found] at h
  obtain ⟨out, run, typed, eq⟩ := (core_run_iff (allocated_toCore found) ready).mp h
  exact ⟨out, run, typed, by rw [v1_to_lime, lime_to_core caller found, eq], congrArg Core.Config.frame eq⟩

private def retFn : Callee := { localFn with program := .ret [.int .i32 99, result] }
private theorem returnPath : Runs retFn start done :=
  ((Relation.ReflTransGen.single (fact (.enter saved args rfl))).tail
    (fact (.labelReturn saved (retFn.init args) [.int .i32 99, result]))).tail
      (fact (.frameReturn saved (retFn.init args) [.int .i32 99] [result] rfl))

example : Lime1.Execution.Steps limeNoHost
    (v1Config (store retFn) caller a retFn start).toLime (v1Config (store retFn) caller a retFn done).toLime := by
  rw [v1_to_lime, v1_to_lime]
  exact (lime_run_iff (allocated_toLime (allocated retFn)) (show Admitted retFn start from ⟨rfl, rfl⟩)).mpr
    ⟨done, returnPath, rfl, rfl⟩

private def trapFn : Callee := { localFn with program := .unreachable }
private abbrev stopped : State := .trapped []

private theorem trapPath : Runs trapFn start stopped :=
  (((((Relation.ReflTransGen.single (fact (.enter saved args rfl))).tail
    (fact (.unreachable saved (trapFn.init args)))).tail
    (fact (.labelTrap saved (trapFn.init args)))).tail
    (fact (.frameTrap saved (trapFn.init args)))).tail
    (fact (.bubble [.int .i64 200] [.int .i32 300] (by decide)))).tail
    (fact (.bubble [] [.int .i64 200] (by decide)))

example : V1.Execution.Steps v1NoHost
    (v1Config (store trapFn) caller a trapFn start) (v1Config (store trapFn) caller a trapFn stopped) :=
  (v1_run_iff (allocated trapFn) (show Admitted trapFn start from ⟨rfl, trivial⟩)).mpr
    ⟨stopped, trapPath, trivial, rfl⟩

example (target : Core.Config Unit) :
    ¬ Core.Step Numerics.Profile.spec noHost
      (coreConfig (store trapFn |>.mapCode V1.Func.toLime |>.toCore) caller a trapFn stopped) target :=
  Core.Step.trap_stuck

example (target : Core.Config Unit) :
    ¬ Core.Step Numerics.Profile.spec noHost
      (coreConfig (store localFn |>.mapCode V1.Func.toLime |>.toCore) caller a localFn done) target :=
  Core.Step.result_stuck (.values ((saved ++ [result]).map Runtime.Value.toCore))

-- An isolated resolved call with zero operands joins the preceding resolution slice.
private def nullary : Callee :=
  ⟨calleeModule, ⟨0⟩, [], [], none, .locals []⟩

example : V1.Execution.Step v1NoHost
    (CallResolution.v1Config (store nullary) caller (.call ⟨0⟩))
    (v1Config (store nullary) caller a nullary (.invoke [] [])) :=
  CallResolution.v1_step_iff.mpr ⟨a, CallResolution.resolves rfl, rfl⟩
