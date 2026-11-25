module

public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Indexed.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Indexed

open Execution.Runtime (Value)

theorem check_source_iff {site : Site} {locals args : List Value} {body : Body} :
    site.checkSource locals args body = true ↔ Admitted site (.source locals args body) :=
  Proofs.check_source_iff

theorem closed {site : Site} {a b : State} (ready : Admitted site a) (edge : Edge site a b) :
    Admitted site b :=
  Proofs.closed ready edge

end Silmaril.Wasm.Institution.Operational.Blocks.Indexed
