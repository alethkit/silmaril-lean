module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (Value)

theorem fact {fn : Callee} {a b : State} (rule : Ground fn a b) : Edge fn a b :=
  Derives.apply (R := (presentation fn).rules) (r := ⟨[], .call a b⟩) (.fact rule) (fun _ h => nomatch h)

theorem reduce {fn : Callee} (saved : List Value) {a b : Locals.State} (step : Locals.Edge a b) :
    Edge fn (.label saved a.locals (.code (.locals a.code)))
      (.label saved b.locals (.code (.locals b.code))) := Proofs.reduce saved step

theorem closed {fn : Callee} {a b : State} (guard : Admitted fn a) (step : Edge fn a b) :
    Admitted fn b := Proofs.closed guard step

theorem saved_of_live {fn : Callee} {a b : State} (edge : Edge fn a b)
    (live : ∀ xs, a ≠ .trapped xs) : b.saved = a.saved :=
  Proofs.saved_of_live edge live

end Silmaril.Wasm.Institution.Operational.CallFrame
