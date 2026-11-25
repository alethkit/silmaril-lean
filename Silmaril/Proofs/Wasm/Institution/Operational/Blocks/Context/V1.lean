module

public import Silmaril.Wasm.Institution.Operational.Blocks.Context.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Context.Lime1
import Silmaril.Wasm.V1.Execution.Inversion
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Context.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (AdminInstr Frame Value)

theorem label_iff {H : Type} {s : Store H} {f : Frame} {n : Nat} {cont : Wasm.V1.Expr}
    {saved : List Value} {body rest : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost ⟨s, f, values saved ++ .label n cont body :: rest⟩ dst ↔
      (∃ mid, Step CallFrame.v1NoHost ⟨s, f, body⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ .label n cont mid.code :: rest⟩) ∨
      ∃ out, PureStep [.label n cont body] out ∧ dst = ⟨s, f, values saved ++ out ++ rest⟩ := by
  constructor
  · intro step
    rcases step.label_inv rfl with ⟨code, inside, eq⟩ | ⟨out, pop, sameStore, sameFrame, eq⟩
    · exact .inl ⟨_, inside, by cases dst; simp_all⟩
    · exact .inr ⟨out, pop, by cases dst; simp_all⟩
  · rintro (⟨⟨_, _, _⟩, move, rfl⟩ | ⟨out, pop, rfl⟩)
    · simpa only [List.append_assoc, List.singleton_append] using Step.context (.label move n cont) saved rest
    · simpa only [List.append_assoc, List.singleton_append] using
        Step.context (Step.pure (host := CallFrame.v1NoHost) s f pop) saved rest

theorem frame_iff {H : Type} {s : Store H} {f callee : Frame} {n k : Nat}
    {saved : List Value} {body rest : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost ⟨s, f, values saved ++ .label n [] [.frame k callee body] :: rest⟩ dst ↔
      ∃ mid, Step CallFrame.v1NoHost ⟨s, f, [.frame k callee body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ .label n [] mid.code :: rest⟩ := by
  rw [label_iff]
  constructor
  · rintro (inside | ⟨out, pop, _⟩)
    · exact inside
    · have projected : Wasm.Lime1.Execution.PureStep f.module.types
          [.label n [] (Wasm.Lime1.Execution.values [] ++ .frame k callee (codeToLime body) :: [])]
          (codeToLime out) := pop.toLime f.module.types
      exact (CallContinuation.OuterCall.Computed.lime_label_stays rfl (by simp) (by simp) (by simp) projected).elim
  · exact Or.inl

theorem result_iff {H : Type} {s : Store H} {f : Frame} {scope : Scope Admin}
    {r : CallContinuation.Nested.Result} {dst : Config H} :
    let code := CallContinuation.Nested.resultCode values .trap r
    Step CallFrame.v1NoHost ⟨s, f, scope.plug values (fun n => .label n []) code⟩ dst ↔
      dst = ⟨s, f, values scope.saved ++ code ++ scope.rest⟩ := by
  constructor
  · intro step
    let other : Scope Wasm.Lime1.Execution.Admin := ⟨scope.arity, scope.saved, codeToLime scope.rest⟩
    have moved := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    have mapResult :
        codeToLime (CallContinuation.Nested.resultCode values .trap r) =
          CallContinuation.Nested.resultCode Wasm.Lime1.Execution.values .trap r := by
      cases r with
      | values stack => exact map_values stack
      | trap => rfl
    have exactStep := (Lime1.result_iff (scope := other) (r := r) (dst := dst.toLime)).mp
      (by simpa only [Config.toLime, Scope.plug, codeToLime_append, map_values, codeToLime_cons,
        AdminInstr.map, List.map_nil, mapResult, other] using moved)
    exact CallContinuation.config_toLime_injective H (by
      simpa only [Config.toLime, codeToLime_append, map_values, mapResult, other] using exactStep)
  · rintro rfl
    apply label_iff.mpr
    cases r with
    | values stack => exact .inr ⟨_, .labelDone _ [] stack, rfl⟩
    | trap => exact .inr ⟨_, .labelTrap _ [], rfl⟩

private def toLime : Returning Admin → Returning Wasm.Lime1.Execution.Admin
  | .pending stack rest => .pending stack (codeToLime rest)
  | .under scope body => .under ⟨scope.arity, scope.saved, codeToLime scope.rest⟩ (toLime body)

private theorem map_code (a : Returning Admin) : codeToLime (v1Code a) = limeCode (toLime a) := by
  induction a with
  | pending stack rest =>
    simp only [toLime, v1Code, limeCode, Returning.render, codeToLime_append, map_values, codeToLime_cons]
    rfl
  | under scope body ih =>
    change codeToLime (values scope.saved ++ .label scope.arity [] (v1Code body) :: scope.rest) = _
    simp only [codeToLime_append, map_values, codeToLime_cons, AdminInstr.map, List.map_nil, ih]
    rfl

private theorem reflect {a : Returning Admin} {out : Returning Wasm.Lime1.Execution.Admin}
    (step : ReturnStep (toLime a) out) : ∃ b, ReturnStep a b ∧ out = toLime b := by
  induction a generalizing out with
  | pending => cases step
  | under scope a ih =>
    cases a with
    | pending stack rest =>
      cases step with
      | exit => exact ⟨_, .exit scope stack rest, rfl⟩
      | under =>
        rename_i _ impossible
        cases impossible
    | under nested inner =>
      cases step with
      | under =>
        rename_i _ innerMove
        obtain ⟨b, h, rfl⟩ := ih innerMove
        exact ⟨_, .under scope h, rfl⟩

private theorem sound {H : Type} {s : Store H} {f : Frame} {a b : Returning Admin}
    (step : ReturnStep a b) : Step CallFrame.v1NoHost ⟨s, f, v1Code a⟩ ⟨s, f, v1Code b⟩ := by
  induction step with
  | exit scope stack rest =>
    apply label_iff.mpr
    have pop := PureStep.labelReturn scope.arity [] stack rest
    refine .inr ⟨_, by simpa only [v1Code, Returning.render, List.append_assoc, List.singleton_append] using pop, ?_⟩
    simp [v1Code, Returning.render, values_append, List.append_assoc]
  | under scope _ ih => exact label_iff.mpr (.inl ⟨_, ih, rfl⟩)

theorem return_step_iff {H : Type} {s : Store H} {f : Frame}
    (a : Returning Admin) {dst : Config H} :
    Step CallFrame.v1NoHost ⟨s, f, v1Code a⟩ dst ↔
      ∃ b, ReturnStep a b ∧ dst = ⟨s, f, v1Code b⟩ := by
  constructor
  · intro step
    have moved := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    obtain ⟨out, h, eq⟩ := (Lime1.return_step_iff (toLime a)).mp
      (by simpa only [Config.toLime, map_code] using moved)
    obtain ⟨b, step, rfl⟩ := reflect h
    exact ⟨b, step, CallContinuation.config_toLime_injective H
      (by simpa only [Config.toLime, map_code] using eq)⟩
  · rintro ⟨b, h, rfl⟩
    exact sound h

end Silmaril.Wasm.Institution.Operational.Blocks.Context.Proofs.V1
