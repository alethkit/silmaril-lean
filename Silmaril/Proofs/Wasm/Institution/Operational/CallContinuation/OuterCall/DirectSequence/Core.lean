module

public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)
open StraightLine
open Computed (coreSyntax)
open Computed.Sequence (coreSource)

theorem body_expression (p : Program) :
    expression p.coreFunc.body = Sequence.coreCode p.site.body (.running [] p.code) := by
  change (p.body coreSource).map Admin.plain = p.body coreSyntax
  simp only [Program.body, List.map_map]
  apply List.map_congr_left
  intro op _
  cases op with
  | numeric op => cases op <;> rfl
  | call => rfl

private theorem enter_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {p : Program} {dst : Config H} (g : CoreGuard s caller p) :
    Step P noHost (coreConfig s caller p.site .invoke) dst ↔
      dst = coreConfig s caller p.site (.label (.running [] p.code)) := by
  have enter := Computed.Sequence.wasm_entry_iff (P := P) (caller := caller) (dst := dst)
    g.allocated g.typed.args
  have init := Computed.Sequence.core_frame_forCall p.site.module p.site.args p.site.locals
  change Frame.forCall p.site.module.toCore (p.site.args.map Value.toCore) p.coreFunc.locals = p.site.frame.toCore at init
  rw [init, body_expression] at enter
  exact enter

theorem sound {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {p : Program} {a b : State p.site} (g : CoreGuard s caller p) (edge : Edge p a b) :
    Step P noHost (coreConfig s caller p.site a) (coreConfig s caller p.site b) := by
  cases invert edge with
  | body move => exact .ctxtFrame (.ctxtLabel (Sequence.core_sound g.body move))
  | ground move =>
    cases move with
    | resolve => exact (Computed.core_direct_call_iff g.resolves g.allocated).mpr rfl
    | enter => exact (enter_iff g).mpr rfl
    | leaveLabel result =>
      cases result with
      | values stack =>
        have exit : Step P noHost
            ⟨s, caller.toCore, [.frame p.site.arity p.site.frame.toCore [.label p.site.arity [] (coreValues stack)]]⟩
            (coreConfig s caller p.site (.exit (.values stack))) := .ctxtFrame .labelVals
        simpa only [coreConfig, coreCode, render, Sequence.coreCode, Sequence.render, List.map_nil, List.append_nil] using exit
      | trap => exact .ctxtFrame .trapLabel
    | leaveFrame result arity =>
      cases result with
      | values => exact .frameVals (by simpa [vals, ResultArity] using arity)
      | trap => exact .trapFrame

theorem readback {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {p : Program} {a : State p.site} {dst : Config H} (g : CoreGuard s caller p)
    (ready : Admitted p.site a) (step : Step P noHost (coreConfig s caller p.site a) dst) :
    ∃ out, Edge p a out ∧ dst = coreConfig s caller p.site out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (Computed.core_direct_call_iff g.resolves g.allocated).mp step⟩
  | invoke => exact ⟨_, fact .enter, (enter_iff g).mp step⟩
  | label q =>
    rcases Computed.core_body_step_cases step with ⟨mid, move, eq⟩ | ⟨_, pop, eq⟩
    · obtain ⟨out, edge, rfl⟩ := (Sequence.core_step_iff g.body ready).mp move
      exact ⟨.label out, underLabel edge, eq⟩
    · obtain ⟨result, finished, rfl⟩ := Sequence.core_label_result ready pop
      exact ⟨.exit result, fact (.leaveLabel (by cases finished <;> constructor)), eq⟩
  | exit result =>
    exact ⟨.done result, fact (.leaveFrame result (result_arity ready)), Nested.core_frame_result (caller := caller) step⟩
  | done result => exact (Nested.core_result_stuck step).elim

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs.Core
