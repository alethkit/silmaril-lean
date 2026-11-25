module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed

open Silmaril.Semantics.SOS

theorem fact {site : Site} {a b : State site} (rule : Ground site a b) : Edge site a b :=
  Derives.apply (R := (presentation site).rules) (r := ⟨[], .step a b⟩)
    (.ground rule) (by simp)

theorem delegate {site : Site} {a b : Nested.State}
    (rule : Nested.Edge site.inner site.arity a b) : Edge site (.nested a) (.nested b) :=
  Proofs.delegate rule

theorem closed {site : Site} (typed : Typed site) {a b : State site}
    (admitted : Admitted site a) (edge : Edge site a b) : Admitted site b :=
  Proofs.closed typed admitted edge

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
