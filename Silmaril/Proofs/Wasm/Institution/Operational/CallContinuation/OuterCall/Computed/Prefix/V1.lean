module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame Value)

@[local simp] private theorem values_one (v : Value) : values [v] = [value v] := rfl

@[local simp] private theorem values_two (a b : Value) : values [a, b] = [value a, value b] := rfl

theorem sound {H : Type} {s : Store H} {f : Frame} {stack : List Value} {op : Op}
    {suffix : List Admin} {ans : Outcome} (step : Reduce f.locals stack op ans) :
    Step CallFrame.v1NoHost ⟨s, f, values stack ++ emit v1Syntax op :: suffix⟩
      ⟨s, f, outcomeCode values .trap suffix ans⟩ := by
  cases step with
  | get found =>
    simpa [outcomeCode, emit, v1Syntax, List.append_assoc] using
      Step.context (Step.localGet (host := CallFrame.v1NoHost) s f _ _ found) stack suffix
  | bin ok =>
    simpa [outcomeCode, emit, v1Syntax, List.append_assoc] using
      Step.context (Step.pure (host := CallFrame.v1NoHost) s f (.intBinary _ _ _ _ _ ok)) _ suffix
  | trap err =>
    simpa [outcomeCode, emit, v1Syntax, List.append_assoc] using
      Step.context (Step.pure (host := CallFrame.v1NoHost) s f (.intBinaryTrap _ _ _ _ _ err)) _ suffix

private theorem code_map_values (xs : List Value) (tail : List Admin) :
    codeToLime (values xs ++ tail) = Wasm.Lime1.Execution.values xs ++ codeToLime tail := by
  rw [codeToLime_append, map_values]

theorem readback {H : Type} {s : Store H} {f : Frame} {stack : List Value} {op : Op}
    {suffix : List Admin} {dst : Config H}
    (step : Step CallFrame.v1NoHost ⟨s, f, values stack ++ emit v1Syntax op :: suffix⟩ dst) :
    ∃ ans, Reduce f.locals stack op ans ∧ dst = ⟨s, f, outcomeCode values .trap suffix ans⟩ := by
  have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
  have source : Config.toLime (⟨s, f, values stack ++ emit v1Syntax op :: suffix⟩ : Config H) =
      ⟨s.mapCode Wasm.V1.Func.toLime, f, Wasm.Lime1.Execution.values stack ++
        emit limeSyntax op :: codeToLime suffix⟩ := by
    simp only [Config.toLime, code_map_values]
    cases op <;> rfl
  rw [source] at mapped
  obtain ⟨ans, reduction, eq⟩ := Computed.Proofs.Lime1.prefix_read mapped
  refine ⟨ans, reduction, CallContinuation.Proofs.config_toLime_injective H (eq.trans ?_)⟩
  cases ans with
  | values => simp only [outcomeCode, Config.toLime, code_map_values]
  | trap =>
    simp only [outcomeCode, Config.toLime, code_map_values]
    rfl

private theorem trap_to_lime {A H : Type} (s : Store H) (f : Frame) (stack : List Value)
    (emitTail : A → Admin) (tail : List A) :
    Config.toLime (⟨s, f, values stack ++ .trap :: tail.map emitTail⟩ : Config H) =
      ⟨s.mapCode Wasm.V1.Func.toLime, f, Wasm.Lime1.Execution.values stack ++ .trap ::
        tail.map (Execution.Runtime.AdminInstr.map Wasm.V1.Instr.toLime ∘ emitTail)⟩ := by
  have mapped : codeToLime (tail.map emitTail) =
      tail.map (Execution.Runtime.AdminInstr.map Wasm.V1.Instr.toLime ∘ emitTail) := by
    change Execution.Runtime.AdminInstr.mapList Wasm.V1.Instr.toLime _ = _
    rw [Execution.Runtime.AdminInstr.mapList_eq_map, List.map_map]
  simp only [Config.toLime, code_map_values, codeToLime_cons, mapped]
  rfl

theorem discard_readback {A H : Type} {s : Store H} {f : Frame} (emitTail : A → Admin)
    {stack : List Value} {tail : List A} {dst : Config H}
    (step : Step CallFrame.v1NoHost ⟨s, f, values stack ++ .trap :: tail.map emitTail⟩ dst) :
    ∃ kept rest, Discard stack tail kept rest ∧
      dst = ⟨s, f, values kept ++ .trap :: rest.map emitTail⟩ := by
  have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
  rw [trap_to_lime] at mapped
  obtain ⟨kept, rest, cut, eq⟩ := Computed.Proofs.Lime1.prefix_discard_read _ mapped
  exact ⟨kept, rest, cut, CallContinuation.Proofs.config_toLime_injective H
    (eq.trans (trap_to_lime s f kept emitTail rest).symm)⟩

theorem discard_sound {A H : Type} {s : Store H} {f : Frame} (emitTail : A → Admin)
    {stack kept : List Value} {tail rest : List A} (step : Discard stack tail kept rest) :
    Step CallFrame.v1NoHost ⟨s, f, values stack ++ .trap :: tail.map emitTail⟩
      ⟨s, f, values kept ++ .trap :: rest.map emitTail⟩ := by
  cases step with
  | cut kept removed cut rest nz =>
    cases removed with
    | nil =>
      cases cut with
      | nil => cases nz <;> contradiction
      | cons head cut =>
        simpa [List.append_assoc] using Step.context
          (Step.pure (host := CallFrame.v1NoHost) s f (.trapTail (emitTail head) (cut.map emitTail)))
          kept (rest.map emitTail)
    | cons v vs =>
      simpa [List.append_assoc] using Step.context
        (Step.pure (host := CallFrame.v1NoHost) s f (.trapValues v vs (cut.map emitTail)))
        kept (rest.map emitTail)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Proofs.V1
