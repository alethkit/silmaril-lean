module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Transport
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs.V1

open Execution
open Execution.Runtime (Frame Value)

theorem v1_sound {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : CallSite}
    {a b : State} (g : V1Guard s caller site) (edge : Edge site a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller site a) (v1Config s caller site b) := by
  open Wasm.V1.Execution in
  cases invert edge with
  | ground h =>
    cases h with
    | resolve =>
      simpa only [v1Config, List.append_nil] using
        Step.context (Step.call (host := CallFrame.v1NoHost) s caller _ _ g.outerLookup) site.args []
    | enter =>
      have count : site.args.length = site.callee.type.params.length := by
        simpa [Outer.type] using (congrArg List.length g.typed.outerArgs)
      have results : site.callee.type.results.length ≤ 1 := by
        cases site.callee.inner.result <;> simp [Outer.type]
      have expr : expression (v1Func site.callee).body =
          values site.callee.innerArgs ++ [.source (.call site.callee.innerIndex), .source .nop] := by
        have one (v : Value) : Locals.v1Codec.emit (.value v) = value v := by
          rcases v with ⟨ty, bits⟩
          cases ty <;> rfl
        change expression ((Locals.values site.callee.innerArgs).map Locals.v1Instr ++
          [.call site.callee.innerIndex, .nop]) = _
        simp only [expression, List.map_append, List.map_cons, List.map_nil, List.map_map]
        change Locals.v1Codec.encode (Locals.values site.callee.innerArgs) ++ _ = _
        simp [Locals.Codec.encode, Locals.values, values, List.map_map, one]
      have locs : (v1Func site.callee).locals = site.callee.locals := rfl
      have h := Step.invokeWasm (host := CallFrame.v1NoHost) s caller _ _ _ _ site.args g.outerAlloc count results
      simpa only [v1Config, expr, Outer.type, Outer.arity, Outer.frame, CallFrame.Callee.arity, locs] using h
    | resolveInner =>
      have step := Step.call (host := CallFrame.v1NoHost) s (site.callee.frame site.args) _ _ g.innerLookup
      have whole := Step.frame (Step.label (Step.context step site.callee.innerArgs [.source .nop])
        site.callee.arity []) site.callee.arity caller
      simpa only [v1Config, CallSite.start, Nested.v1Config, Nested.v1Code, Nested.render, CallContinuation.v1Code,
        CallContinuation.render, CallFrame.v1Code, CallFrame.legacyCode, values, List.nil_append,
        List.append_assoc, List.singleton_append] using whole
  | nest h => exact Nested.v1_sound g.innerAlloc h

theorem v1_step_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : CallSite}
    {a : State} {b : Wasm.V1.Execution.Config H} (g : V1Guard s caller site) (ready : Admitted site a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = v1Config s caller site out := by
  constructor
  · intro step
    have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    rw [v1_to_lime] at mapped
    obtain ⟨out, edge, eq⟩ := (Lime1.lime_step_iff (guard_to_lime g) ready).mp mapped
    exact ⟨out, edge, CallContinuation.Proofs.config_toLime_injective H (eq.trans (v1_to_lime s caller site out).symm)⟩
  · rintro ⟨out, move, rfl⟩
    exact v1_sound g move

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs.V1
