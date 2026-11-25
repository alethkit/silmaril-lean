module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall

open Silmaril.Semantics.SOS

theorem fact {site : CallSite} {a b : State} (rule : Ground site a b) : Edge site a b :=
  Derives.apply (R := (presentation site).rules) (r := ⟨[], .transition a b⟩)
    (.ground rule) (fun _ h => nomatch h)

theorem delegate {site : CallSite} {a b : Nested.State}
    (inner : Nested.Edge site.callee.inner site.callee.arity a b) : Edge site (.nested a) (.nested b) :=
  Proofs.delegate inner

theorem closed {site : CallSite} (typed : Typed site) {a b : State}
    (admitted : Admitted site a) (edge : Edge site a b) : Admitted site b :=
  Proofs.closed typed admitted edge

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
