module

public import Silmaril.Wasm.Institution.Operational.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational

open CategoryTheory Silmaril.Logic.Operational
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

@[simp] theorem decode_encode {H : Type} (c : Config H) :
    decode (encode c) = c := rfl

@[simp] theorem encode_decode {H : Type} (c : (WasmShape.signatures.obj (shape H)).State) :
    encode (decode c) = c := rfl

/-- Satisfaction of an encoded edge is exactly Core reduction at that edge. -/
theorem step_iff {H : Type} (P : Profile) (host : HostSemantics H) (s t : Config H) :
    (system P host).model (encode s, (), encode t) ↔ Step P host s t :=
  Iff.rfl

end Silmaril.Wasm.Institution.Operational
