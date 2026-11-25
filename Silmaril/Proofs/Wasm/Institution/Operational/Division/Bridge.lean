module

public import Silmaril.Wasm.Institution.Operational.Division.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.Division.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Division.Proofs

open CategoryTheory Silmaril.Logic.Operational
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Profile}

theorem runs_readback {s t : (WasmShape.signatures.obj (Operational.shape H)).State}
    {labels : List Unit} (path : Runs (Operational.system P (noHost (H := H))).model s labels t)
    (supported : Admitted (decode s)) :
    Runs (transitionSystem H).model (decode s) labels (decode t) := by
  induction path with
  | refl => exact .refl
  | stepL step _ ih =>
    have rule := step_readback supported step
    exact .stepL rule (ih (derives_admitted rule).2)

theorem policy_safe {s : Config H} (supported : Admitted s) : (policy H).SafeAt s := by
  rintro ⟨t, path, bad⟩
  induction path with
  | refl => exact bad supported
  | tail _ step _ => exact bad (derives_admitted step).2

end Silmaril.Wasm.Institution.Operational.Division.Proofs
