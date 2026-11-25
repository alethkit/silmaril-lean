module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Transport
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame FuncAddr)

theorem sound {H : Type} {s : Store H} {caller outer : Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a b : State} (e : Edge fn arity a b) :
    Step CallFrame.v1NoHost (v1Config s caller outer addr fn arity a)
      (v1Config s caller outer addr fn arity b) := by
  cases invert e with
  | context move => exact .frame (.label (CallContinuation.v1_sound allocated move) arity []) arity caller
  | ground h =>
    cases h with
    | labelValues stack => exact .frame (.pure s outer (.labelDone arity [] stack)) arity caller
    | labelTrap => exact .frame (.pure s outer (.labelTrap arity [])) arity caller
    | frameValues stack h => exact .pure s caller (.frameDone arity outer stack h)
    | frameTrap => exact .pure s caller (.frameTrap arity outer)

theorem readback {H : Type} {s : Store H} {caller outer : Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {dst : Config H} (guard : Admitted fn a)
    (step : Step CallFrame.v1NoHost (v1Config s caller outer addr fn arity a) dst) :
    ∃ out, Edge fn arity a out ∧ dst = v1Config s caller outer addr fn arity out := by
  have translated := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ impossible => impossible)
  rw [Proofs.v1_to_lime] at translated
  obtain ⟨out, edge, eq⟩ := Proofs.Lime1.readback (CallFrame.allocated_toLime allocated) guard translated
  exact ⟨out, edge, CallContinuation.Proofs.config_toLime_injective H
    (eq.trans (Proofs.v1_to_lime s caller outer addr fn arity out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs.V1
