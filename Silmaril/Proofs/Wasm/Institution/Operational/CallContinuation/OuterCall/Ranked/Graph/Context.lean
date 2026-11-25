module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs

open Execution
open Execution.Runtime (AdminInstr Frame Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

theorem core_entered_child_iff {H : Type} {P : Profile} {s : Core.Store H} {caller parent child : Core.Frame}
    {n k m : Nat} {cont : List Instr} {saved : List Core.Val} {body rest : List Core.Admin} {dst : Core.Config H} :
    Core.Step P noHost
      ⟨s, caller, [.frame n parent [.label m cont (Core.vals saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Core.Step P noHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label m cont (Core.vals saved ++ mid.code ++ rest)]]⟩ := by
  constructor
  · intro step
    rcases Computed.core_body_step_cases step with ⟨mid, inside, eq⟩ | ⟨_, pop, _⟩
    · obtain ⟨out, move, rfl⟩ := Core.Step.ctx_in_seq (X := .frame k child body) (by simp [Core.Admin.IsCtx]) inside
      exact ⟨out, move, eq⟩
    · exact (Computed.core_label_stays (head := .frame k child body) rfl
        (by simp) (by simp) (by simp [Core.Admin.IsReturnCallRef]) (by simp) (by simp) pop).elim
  · rintro ⟨⟨_, _, _⟩, inside, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using
      Core.Step.ctxtFrame (f := caller) (n := n)
        (Core.Step.ctxtLabel (n := m) (cont := cont) (Core.Sim.Step.vals_left (Core.Sim.Step.append_right inside rest) saved))

open Wasm.Lime1.Execution in
theorem lime_entered_child_iff {H : Type} {s : Store H} {caller parent child : Frame}
    {n k m : Nat} {cont : Wasm.Lime1.Expr} {saved : List Value} {body rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost
      ⟨s, caller, [.frame n parent [.label m cont (values saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Step CallFrame.limeNoHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label m cont (values saved ++ mid.code ++ rest)]]⟩ := by
  constructor
  · intro step
    rcases Computed.lime_body_step_cases step with ⟨mid, inside, eq⟩ | ⟨_, pop, _⟩
    · obtain ⟨out, move, rfl⟩ := CallContinuation.lime_frame_context_inv inside
      exact ⟨out, move, eq⟩
    · exact (Computed.lime_label_stays (head := .frame k child body) rfl
        (by simp) (by simp) (by simp) pop).elim
  · rintro ⟨⟨_, _, _⟩, inside, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using
      Step.frame (.label (.context inside saved rest) m cont) n caller

open Wasm.V1.Execution in
theorem v1_entered_child_iff {H : Type} {s : Store H} {caller parent child : Frame}
    {n k : Nat} {saved : List Value} {body rest : List Admin} {dst : Config H}
    (reflectChild : ∀ out, Wasm.Lime1.Execution.Step CallFrame.limeNoHost
        (Config.toLime (⟨s, parent, [.frame k child body]⟩ : Config H)) out →
      ∃ mid, Step CallFrame.v1NoHost ⟨s, parent, [.frame k child body]⟩ mid ∧ mid.toLime = out) :
    Step CallFrame.v1NoHost
      ⟨s, caller, [.frame n parent [.label n [] (values saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Step CallFrame.v1NoHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] (values saved ++ mid.code ++ rest)]]⟩ := by
  constructor
  · intro step
    have projected := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    simp only [Config.toLime, codeToLime_cons, codeToLime_nil, AdminInstr.map, codeToLime_append, map_values]
      at projected
    obtain ⟨out, move, eq⟩ := lime_entered_child_iff.mp projected
    obtain ⟨mid, native, rfl⟩ := reflectChild out move
    refine ⟨mid, native, CallContinuation.config_toLime_injective H ?_⟩
    simpa only [Config.toLime, codeToLime_cons, codeToLime_nil, AdminInstr.map, codeToLime_append, map_values,
      List.append_assoc, List.map_nil] using eq
  · rintro ⟨⟨_, _, _⟩, inside, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using
      Step.frame (.label (.context inside saved rest) n []) n caller

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
