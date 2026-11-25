module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation

open Silmaril.Semantics.SOS

theorem fact {fn : CallFrame.Callee} {a b : State} (rule : Ground a b) : Edge fn a b :=
  Derives.apply (R := (presentation fn).rules) (r := ⟨[], .outer a b⟩) (.ground rule) (fun _ h => nomatch h)

theorem call {fn : CallFrame.Callee} {a b : CallFrame.State} (live : Active a)
    (inner : CallFrame.Edge fn a b) : Edge fn (.active a) (attach b) := Proofs.call live inner

theorem closed {fn : CallFrame.Callee} {a b : State} (guard : Admitted fn a) (edge : Edge fn a b) :
    Admitted fn b := Proofs.closed guard edge

end Silmaril.Wasm.Institution.Operational.CallContinuation
