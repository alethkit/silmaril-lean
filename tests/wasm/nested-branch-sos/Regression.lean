module

import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value)
open Silmaril.Wasm.Institution.Operational.BranchExit

private def below : List Value := [.int .i64 41, .int .i32 7]
private def payload : List Value := [.int .i32 42]
private def ty : Option NumType := some (.int .i32)
private def start : State := .nested 0 below payload
private def middle : State := .outer below payload
private def final : State := .done payload
private def store : V1.Execution.Store Unit := {}
private def frame : Frame := ⟨[.int .i64 20], {}⟩
private def v1Host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def limeHost : Lime1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def coreHost : Core.HostSemantics Unit := fun _ _ _ _ => False
private abbrev limeStore := store.mapCode V1.Func.toLime

private theorem cross : Edge ty start middle := fact (.cross 0 below payload)
private theorem finish : Edge ty middle final := fact (.finish below payload rfl)
private theorem typed : Admitted ty start := rfl

example : V1.Execution.Step v1Host (v1Config store frame ty start) (v1Config store frame ty middle) :=
  v1_sound cross

example : (v1Config store frame ty middle).code =
    [.label 1 [] [.source (.intConst .i64 41), .source (.intConst .i32 7),
      .source (.intConst .i32 42), .source (.br ⟨0⟩)]] := rfl

example : Lime1.Execution.Step limeHost (v1Config store frame ty middle).toLime
    (v1Config store frame ty final).toLime := by
  rw [v1_to_lime, v1_to_lime]
  exact lime_sound finish

example : Core.Steps Numerics.Profile.spec coreHost (v1Config store frame ty start).toLime.toCore
    ⟨limeStore.toCore, frame.toCore, [.plain (.intConst .i32 42)]⟩ := by
  rw [v1_to_lime, lime_to_core]
  exact (.tail (.single (core_sound cross)) (core_sound finish))

example {target : Core.Config Unit} (h : Core.Steps Numerics.Profile.spec coreHost
    (v1Config store frame ty start).toLime.toCore target) :
    ∃ out, Runs ty start out ∧ Admitted ty out ∧
      target = (v1Config store frame ty out).toLime.toCore ∧ target.frame = frame.toCore := by
  rw [v1_to_lime, lime_to_core] at h
  obtain ⟨out, run, guard, eq⟩ := (core_run_iff typed).mp h
  exact ⟨out, run, guard, by rw [v1_to_lime, lime_to_core, eq], congrArg Core.Config.frame eq⟩

example {target : Core.Config Unit} :
    ¬ Core.Step Numerics.Profile.spec coreHost (coreConfig limeStore.toCore frame.toCore ty final) target := by
  intro step
  obtain ⟨_, edge, _⟩ := (core_step_iff (show Admitted ty final from rfl)).mp step
  cases invert edge

example : Edge none (.outer below []) (.done []) := fact (.finish below [] rfl)
