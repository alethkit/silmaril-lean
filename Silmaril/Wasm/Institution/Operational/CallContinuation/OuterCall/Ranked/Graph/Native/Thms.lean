module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Context

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution
open Execution.Runtime (Frame Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

/-- Exact native composition under the parent's function label and frame
when the child has entered its own frame. No bound on the child's code or nesting is needed. -/
theorem core_entered_child_iff {H : Type} {P : Profile} {s : Core.Store H} {caller parent child : Core.Frame}
    {n k : Nat} {saved : List Core.Val} {body rest : List Core.Admin} {dst : Core.Config H} :
    Core.Step P noHost
      ⟨s, caller, [.frame n parent [.label n [] (Core.vals saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Core.Step P noHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] (Core.vals saved ++ mid.code ++ rest)]]⟩ :=
  Proofs.core_entered_child_iff

open Wasm.Lime1.Execution in
/-- The same entered-child boundary for Lime1 preserves the pending suffix at
the parent's label, even on the step that delivers a trap. -/
theorem lime_entered_child_iff {H : Type} {s : Store H} {caller parent child : Frame}
    {n k : Nat} {saved : List Value} {body rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost
      ⟨s, caller, [.frame n parent [.label n [] (values saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Step CallFrame.limeNoHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] (values saved ++ mid.code ++ rest)]]⟩ :=
  Proofs.lime_entered_child_iff

open Wasm.V1.Execution in
/-- Lift reflection of the child's V1 steps along the V1-to-Lime1 projection
through a suspended caller, using the same native context as Lime1. -/
theorem v1_entered_child_iff {H : Type} {s : Store H} {caller parent child : Frame}
    {n k : Nat} {saved : List Value} {body rest : List Admin} {dst : Config H}
    (reflectChild : ∀ out, Wasm.Lime1.Execution.Step CallFrame.limeNoHost
        (Config.toLime (⟨s, parent, [.frame k child body]⟩ : Config H)) out →
      ∃ mid, Step CallFrame.v1NoHost ⟨s, parent, [.frame k child body]⟩ mid ∧ mid.toLime = out) :
    Step CallFrame.v1NoHost
      ⟨s, caller, [.frame n parent [.label n [] (values saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Step CallFrame.v1NoHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] (values saved ++ mid.code ++ rest)]]⟩ :=
  Proofs.v1_entered_child_iff reflectChild

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
