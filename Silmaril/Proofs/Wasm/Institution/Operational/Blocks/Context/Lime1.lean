module

public import Silmaril.Wasm.Institution.Operational.Blocks.Context.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Context.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)

theorem label_iff {H : Type} {s : Store H} {f : Frame} {n : Nat}
    {saved : List Value} {body rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values saved ++ .label n [] body :: rest⟩ dst ↔
      (∃ mid, Step CallFrame.limeNoHost ⟨s, f, body⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ .label n [] mid.code :: rest⟩) ∨
      ∃ out, PureStep f.module.types [.label n [] body] out ∧ dst = ⟨s, f, values saved ++ out ++ rest⟩ := by
  constructor
  · exact CallContinuation.lime_label_context_cases
  · rintro (⟨⟨_, _, _⟩, move, rfl⟩ | ⟨out, pop, rfl⟩)
    · simpa only [List.append_assoc, List.singleton_append] using Step.context (.label move n []) saved rest
    · simpa only [List.append_assoc, List.singleton_append] using
        Step.context (Step.pure (host := CallFrame.limeNoHost) s f pop) saved rest

theorem frame_iff {H : Type} {s : Store H} {f callee : Frame} {n k : Nat}
    {saved : List Value} {body rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values saved ++ .label n [] [.frame k callee body] :: rest⟩ dst ↔
      ∃ mid, Step CallFrame.limeNoHost ⟨s, f, [.frame k callee body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ .label n [] mid.code :: rest⟩ := by
  rw [label_iff]
  constructor
  · rintro (inside | ⟨out, pop, _⟩)
    · exact inside
    · have shaped : PureStep f.module.types [.label n [] (values [] ++ .frame k callee body :: [])] out := pop
      exact (CallContinuation.OuterCall.Computed.lime_label_stays rfl (by simp) (by simp) (by simp) shaped).elim
  · exact Or.inl

theorem result_iff {H : Type} {s : Store H} {f : Frame} {scope : Scope Admin}
    {r : CallContinuation.Nested.Result} {dst : Config H} :
    let code := CallContinuation.Nested.resultCode values .trap r
    Step CallFrame.limeNoHost ⟨s, f, scope.plug values (fun n => .label n []) code⟩ dst ↔
      dst = ⟨s, f, values scope.saved ++ code ++ scope.rest⟩ := by
  dsimp only [Scope.plug]
  rw [label_iff]
  constructor
  · rintro (⟨_, inside, _⟩ | ⟨out, pop, rfl⟩)
    · exact (CallContinuation.Nested.lime_result_stuck inside).elim
    · rw [CallContinuation.Nested.lime_label_result pop]
  · rintro rfl
    cases r with
    | values vs => exact .inr ⟨_, .labelDone _ [] vs, rfl⟩
    | trap => exact .inr ⟨_, .labelTrap _ [], rfl⟩

theorem return_step_iff {H : Type} {s : Store H} {f : Frame}
    (a : Returning Admin) {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, limeCode a⟩ dst ↔
      ∃ b, ReturnStep a b ∧ dst = ⟨s, f, limeCode b⟩ := by
  induction a generalizing dst with
  | pending stack rest =>
    constructor
    · intro h
      exact (CallFrame.lime_return_stuck (stack := stack) (tail := rest) h).elim
    · rintro ⟨_, h, _⟩
      cases h
  | under scope a ih =>
    change Step CallFrame.limeNoHost ⟨s, f, values scope.saved ++ .label scope.arity [] (limeCode a) :: scope.rest⟩ dst ↔ _
    rw [label_iff]
    constructor
    · rintro (⟨mid, inside, rfl⟩ | ⟨out, pop, rfl⟩)
      · obtain ⟨b, h, rfl⟩ := ih.mp inside
        exact ⟨.under scope b, .under scope h, rfl⟩
      · cases a with
        | pending stack rest =>
          have eq := CallFrame.lime_return_label_result (stack := stack) (tail := rest) pop
          refine ⟨_, .exit scope stack rest, ?_⟩
          simp [eq, limeCode, Returning.render, values_append, List.append_assoc]
        | under nested inner =>
          exact (CallContinuation.OuterCall.Computed.lime_label_stays
            (head := .label nested.arity [] (limeCode inner)) rfl (by simp) (by simp) (by simp) pop).elim
    · rintro ⟨b, h, rfl⟩
      cases h with
      | exit scope stack rest =>
        have pop := PureStep.labelReturn (types := f.module.types) scope.arity [] stack rest
        refine .inr ⟨_, by simpa only [limeCode, Returning.render, List.append_assoc, List.singleton_append] using pop, ?_⟩
        simp [limeCode, Returning.render, values_append, List.append_assoc]
      | under scope inner => exact .inl ⟨_, ih.mpr ⟨_, inner, rfl⟩, rfl⟩

end Silmaril.Wasm.Institution.Operational.Blocks.Context.Proofs.Lime1
