module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Rules
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs.Core

open Execution.Core
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)
open Execution.Runtime (Value)
open StraightLine

private theorem invocation_stays {ctx : Context} {site : Site} {n : Nat}
    {q : DirectSequence.State site} {tail out : List Admin} (live : Enclosing.Live q)
    (step : LabelExit n [] (coreValues ctx.saved ++ DirectSequence.coreCode site q ++ tail) out) : False := by
  have frame {k : Nat} {inside : Frame} {body : List Admin}
      (code : DirectSequence.coreCode site q = [.frame k inside body]) : False := by
    have h := step
    rw [code, List.append_assoc, List.singleton_append] at h
    exact Computed.core_label_stays (stack := ctx.saved.map Value.toCore) (head := .frame k inside body)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) h
  cases q with
  | label _ | exit _ => exact frame rfl
  | call =>
    have h : LabelExit n [] (vals ((ctx.saved ++ site.args).map Value.toCore) ++ .plain (.call site.index) :: tail) out := by
      simpa only [DirectSequence.coreCode, DirectSequence.render, coreValues, List.map_append, vals_append, List.append_assoc,
        List.singleton_append] using step
    exact Computed.core_label_stays (stack := (ctx.saved ++ site.args).map Value.toCore) (head := .plain (.call site.index))
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) h
  | invoke =>
    have refCode : vals [.ref (.func site.address.value)] = [.ref (.func site.address.value)] := rfl
    have h : LabelExit n [] (vals ((ctx.saved ++ site.args).map Value.toCore ++ [.ref (.func site.address.value)]) ++ .callRefType site.type.toDefType :: tail) out := by
      simpa only [DirectSequence.coreCode, DirectSequence.render, coreValues, List.map_append, vals_append, List.append_assoc,
        List.cons_append, List.nil_append, refCode] using step
    exact Computed.core_label_stays (stack := ((ctx.saved ++ site.args).map Value.toCore ++ [.ref (.func site.address.value)])) (head := .callRefType site.type.toDefType)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) h
  | done _ => exact live.elim

theorem sound {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {ctx : Context} {p : Program} {a b : State ctx p.site} (g : Enclosing.CoreGuard s ctx p)
    (edge : Edge ctx p a b) : Step P noHost (coreConfig s caller ctx p.site a) (coreConfig s caller ctx p.site b) := by
  cases invert edge with
  | body move => exact .ctxtFrame (.ctxtLabel (Enclosing.core_sound g move))
  | ground rule =>
    cases rule with
    | leaveLabel finished =>
      cases finished with
      | values stack =>
        have leave : Step P noHost
            ⟨s, caller.toCore, [.frame ctx.sequence.results.length ctx.frame.toCore
              [.label ctx.sequence.results.length [] (coreValues stack)]]⟩
            (coreConfig s caller ctx p.site (.exit (.values stack))) :=
          .ctxtFrame .labelVals
        simpa only [coreConfig, coreCode, render, Enclosing.coreCode, Enclosing.render, Sequence.coreCode,
          Sequence.render, List.map_nil, List.append_nil] using leave
      | trap => exact .ctxtFrame .trapLabel
    | leaveFrame result arity =>
      cases result with
      | values stack => exact .frameVals (by simpa [vals, Sequence.ResultArity] using arity)
      | trap => exact .trapFrame

theorem readback {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {ctx : Context} {p : Program} {a : State ctx p.site} {dst : Config H} (g : Enclosing.CoreGuard s ctx p)
    (ready : Admitted a) (step : Step P noHost (coreConfig s caller ctx p.site a) dst) :
    ∃ out, Edge ctx p a out ∧ dst = coreConfig s caller ctx p.site out := by
  cases a with
  | label q =>
    rcases Computed.core_body_step_cases step with ⟨mid, bodyStep, eq⟩ | ⟨_, pop, eq⟩
    · obtain ⟨out, move, rfl⟩ := (Enclosing.core_step_iff g ready).mp bodyStep
      exact ⟨.label out, underLabel move, eq⟩
    · cases q with
      | active phase => exact (invocation_stays ready.1 pop).elim
      | continuation phase =>
        obtain ⟨result, finished, rfl⟩ := Sequence.core_label_result ready pop
        exact ⟨.exit result, fact (.leaveLabel finished), eq⟩
  | exit r =>
    exact ⟨.done r, fact (.leaveFrame r (Sequence.result_arity ready)), Nested.core_frame_result (caller := caller) step⟩
  | done r => exact (Nested.core_result_stuck step).elim

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs.Core
