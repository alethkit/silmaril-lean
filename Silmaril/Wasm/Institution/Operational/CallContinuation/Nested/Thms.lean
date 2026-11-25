module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested

open Silmaril.Semantics.SOS

theorem fact {fn : CallFrame.Callee} {arity : Nat} {a b : State} (rule : Ground arity a b) : Edge fn arity a b :=
  Derives.apply (R := (presentation fn arity).rules) (r := ⟨[], .step a b⟩) (.ground rule) (fun _ h => nomatch h)

theorem underLabel {fn : CallFrame.Callee} {arity : Nat} {a b : CallContinuation.State}
    (inner : CallContinuation.Edge fn a b) : Edge fn arity (.label a) (.label b) :=
  Proofs.underLabel inner

theorem closed {fn : CallFrame.Callee} {arity : Nat} {a b : State}
    (guard : Admitted fn a) (edge : Edge fn arity a b) : Admitted fn b :=
  Proofs.closed guard edge

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested
