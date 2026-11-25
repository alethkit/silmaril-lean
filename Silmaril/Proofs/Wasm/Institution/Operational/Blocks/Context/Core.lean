module

public import Silmaril.Wasm.Institution.Operational.Blocks.Context.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Context.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

theorem label_iff {H : Type} {P : Profile} {s : Store H} {f : Frame} {n : Nat}
    {saved : List Val} {body rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals saved ++ .label n [] body :: rest⟩ dst ↔
      (∃ mid, Step P noHost ⟨s, f, body⟩ mid ∧
        dst = ⟨mid.store, mid.frame, vals saved ++ .label n [] mid.code :: rest⟩) ∨
      ∃ out, LabelExit n [] body out ∧ dst = ⟨s, f, vals saved ++ out ++ rest⟩ := by
  constructor
  · intro step
    obtain ⟨mid, move, rfl⟩ := Step.ctx_in_seq (X := .label n [] body) (by simp [Admin.IsCtx]) step
    rcases move.label_inv with ⟨_, _, _, h, rfl⟩ | ⟨out, pop, rfl⟩
    · exact .inl ⟨_, h, by simp only [List.append_assoc, List.singleton_append]⟩
    · exact .inr ⟨out, pop, rfl⟩
  · rintro (⟨⟨_, _, _⟩, move, rfl⟩ | ⟨out, pop, rfl⟩)
    · simpa only [List.append_assoc, List.singleton_append] using
        Sim.Step.vals_left (Sim.Step.append_right (.ctxtLabel (n := n) (cont := []) move) rest) saved
    · have move : Step P noHost ⟨s, f, [.label n [] body]⟩ ⟨s, f, out⟩ := by
        cases pop with
        | vals => exact .labelVals
        | brZero idx count => exact .brLabelZero idx count
        | brSucc idx => exact .brLabelSucc idx
        | ret => exact .returnLabel
        | returnCall isTail => exact .returnCallRefLabel isTail
        | throw => exact .throwRefLabel
        | trap => exact .trapLabel
      simpa only [List.append_assoc, List.singleton_append] using
        Sim.Step.vals_left (Sim.Step.append_right move rest) saved

theorem frame_iff {H : Type} {P : Profile} {s : Store H} {f callee : Frame} {n k : Nat}
    {saved : List Val} {body rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals saved ++ .label n [] [.frame k callee body] :: rest⟩ dst ↔
      ∃ mid, Step P noHost ⟨s, f, [.frame k callee body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, vals saved ++ .label n [] mid.code :: rest⟩ := by
  rw [label_iff]
  constructor
  · rintro (inside | ⟨out, pop, _⟩)
    · exact inside
    · have shaped : LabelExit n [] (vals [] ++ .frame k callee body :: []) out := pop
      exact (CallContinuation.OuterCall.Computed.core_label_stays rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) shaped).elim
  · exact Or.inl

theorem result_iff {H : Type} {P : Profile} {s : Store H} {f : Frame} {scope : Scope Admin}
    {r : CallContinuation.Nested.Result} {dst : Config H} :
    let code := CallContinuation.Nested.resultCode coreValues .trap r
    Step P noHost ⟨s, f, scope.plug coreValues (fun n => .label n []) code⟩ dst ↔
      dst = ⟨s, f, coreValues scope.saved ++ code ++ scope.rest⟩ := by
  dsimp only [Scope.plug]
  rw [label_iff]
  constructor
  · rintro (⟨_, inside, _⟩ | ⟨out, pop, rfl⟩)
    · exact (CallContinuation.Nested.core_result_stuck inside).elim
    · rw [CallContinuation.Nested.core_label_result pop]
  · rintro rfl
    cases r with
    | values vs => exact .inr ⟨_, .vals _, rfl⟩
    | trap => exact .inr ⟨_, .trap, rfl⟩

theorem return_step_iff {H : Type} {P : Profile} {s : Store H} {f : Frame}
    (a : Returning Admin) {dst : Config H} :
    Step P noHost ⟨s, f, coreCode a⟩ dst ↔
      ∃ b, ReturnStep a b ∧ dst = ⟨s, f, coreCode b⟩ := by
  induction a generalizing dst with
  | pending stack rest =>
    constructor
    · intro h
      exact (CallFrame.core_return_stuck (stack := stack.map Value.toCore) (tail := rest) h).elim
    · rintro ⟨_, h, _⟩
      cases h
  | under scope a ih =>
    change Step P noHost ⟨s, f, coreValues scope.saved ++ .label scope.arity [] (coreCode a) :: scope.rest⟩ dst ↔ _
    rw [label_iff]
    constructor
    · rintro (⟨mid, inside, rfl⟩ | ⟨out, pop, rfl⟩)
      · obtain ⟨b, h, rfl⟩ := ih.mp inside
        exact ⟨.under scope b, .under scope h, rfl⟩
      · cases a with
        | pending stack rest =>
          have eq := CallFrame.core_return_label_result (stack := stack.map Value.toCore) (tail := rest) pop
          refine ⟨_, .exit scope stack rest, ?_⟩
          simp [eq, coreCode, Returning.render, coreValues, List.map_append, vals_append, List.append_assoc]
        | under nested inner =>
          exact (CallContinuation.OuterCall.Computed.core_label_stays
            (head := .label nested.arity [] (coreCode inner)) rfl
            (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop).elim
    · rintro ⟨b, h, rfl⟩
      cases h with
      | exit scope stack rest =>
        have pop := LabelExit.ret (n := scope.arity) (cont := []) (vs := stack.map Value.toCore) (rest := rest)
        refine .inr ⟨_, by simpa only [coreCode, Returning.render, List.append_assoc, List.singleton_append] using pop, ?_⟩
        simp [coreCode, Returning.render, coreValues, List.map_append, vals_append, List.append_assoc]
      | under scope inner => exact .inl ⟨_, ih.mpr ⟨_, inner, rfl⟩, rfl⟩

end Silmaril.Wasm.Institution.Operational.Blocks.Context.Proofs.Core
