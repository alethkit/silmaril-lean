module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame FuncAddr)

private abbrev nop : Admin := .source .nop

theorem sound {H : Type} {s : Store H} {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a b : State} (edge : Edge fn a b) :
    Step CallFrame.v1NoHost (v1Config s caller addr fn a) (v1Config s caller addr fn b) := by
  cases invert edge with
  | @call a b _ h =>
    have step := CallFrame.v1_sound (caller := caller) allocated h
    have out : CallFrame.v1Code addr fn b ++ [nop] = v1Code addr fn (attach b) := by
      cases b <;> rfl
    change Step CallFrame.v1NoHost ⟨s, caller, CallFrame.v1Code addr fn a ++ [nop]⟩
      ⟨s, caller, v1Code addr fn (attach b)⟩
    rw [← out]
    exact .context step [] [nop]
  | ground h =>
    cases h with
    | resume stack =>
      simpa only [v1Config, v1Code, render, List.append_nil] using
        (Step.context (Step.pure (host := CallFrame.v1NoHost) s caller .nop) stack [])
    | discardValues kept removed hasTail ne =>
      cases removed with
      | nil => contradiction
      | cons v vs =>
        have h := Step.pure (host := CallFrame.v1NoHost) s caller (PureStep.trapValues v vs [])
        simpa only [v1Config, v1Code, render, values_append, List.append_assoc, List.append_nil] using
          Step.context h kept (tail nop hasTail)
    | discardTail kept removed =>
      cases removed with
      | nil =>
        simpa only [v1Config, v1Code, render, tail, ↓reduceIte, Bool.false_eq_true,
          List.append_nil, List.append_assoc, List.singleton_append] using
          (Step.context (Step.pure (host := CallFrame.v1NoHost) s caller (.trapTail nop [])) kept [])
      | cons v vs =>
        have h := Step.pure (host := CallFrame.v1NoHost) s caller (PureStep.trapValues v vs [nop])
        simpa only [v1Config, v1Code, render, tail, ↓reduceIte, Bool.false_eq_true,
          List.append_nil, values_append, List.append_assoc] using Step.context h kept []

theorem readback {H : Type} {s : Store H} {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {dst : Config H} (ready : Admitted fn a)
    (step : Step CallFrame.v1NoHost (v1Config s caller addr fn a) dst) :
    ∃ out, Edge fn a out ∧ dst = v1Config s caller addr fn out := by
  have translated := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ impossible => impossible)
  rw [Proofs.v1_to_lime] at translated
  obtain ⟨out, edge, eq⟩ := Proofs.Lime1.readback (CallFrame.allocated_toLime allocated) ready translated
  exact ⟨out, edge, config_toLime_injective H (eq.trans (Proofs.v1_to_lime s caller addr fn out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs.V1
