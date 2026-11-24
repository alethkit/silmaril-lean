module

public import Silmaril.Logic.Operational.Machines.Thms
public import Silmaril.Wasm.Execution.Core.Step

/-!
# Operational view of WebAssembly Core

The shape stores the Core administrative configuration losslessly. The model
is the landed Core small-step relation, with the original numeric profile and
host semantics as parameters. The Core relation is unlabelled, so its edge
labels are unit.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational

open CategoryTheory Silmaril.Logic.Operational
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- Store, active frame and ordered Core administrative terms. -/
def shape (H : Type) : WasmShape := ⟨Store H, Frame, Admin, Unit⟩

/-- Convert the public Core configuration without projecting away any field. -/
def encode {H : Type} (c : Config H) : (WasmShape.signatures.obj (shape H)).State :=
  ⟨(c.store, c.frame), c.code⟩

/-- Recover the public Core configuration. -/
def decode {H : Type} (c : (WasmShape.signatures.obj (shape H)).State) : Config H :=
  ⟨c.control.1, c.control.2, c.stack⟩

/-- Package the existing reduction relation as a Wasm-style system. -/
def system {H : Type} (P : Profile) (host : HostSemantics H) : WasmSystem :=
  ⟨shape H, fun e => Step P host (decode e.1) (decode e.2.2)⟩

end Silmaril.Wasm.Institution.Operational
