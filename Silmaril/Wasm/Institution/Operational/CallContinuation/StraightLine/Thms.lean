module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine

open Silmaril.Semantics.SOS

theorem fact {site : Site} {a b : State} (rule : Ground site a b) : Edge site a b :=
  Derives.apply (R := (presentation site).rules) (r := ⟨[], .step a b⟩)
    (.ground rule) (by simp)

theorem call {site : Site} {a b : CallFrame.State} (live : Active a)
    (edge : CallFrame.Edge site.callee a b) : Edge site (.active a) (attach site b) :=
  Proofs.call live edge

theorem closed {site : Site} {a b : State} (ready : Admitted site a) (edge : Edge site a b) :
    Admitted site b :=
  Proofs.closed ready edge

/-- Once the callee has trapped, every finite remaining run stays in trap propagation. -/
theorem callee_trap_bypasses {site : Site} {saved : List Execution.Runtime.Value} {a : State}
    (run : Runs site (attach site (.trapped saved)) a) : Unwinding a :=
  Proofs.callee_trap_bypasses run

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine
