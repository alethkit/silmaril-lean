module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing

open Silmaril.Semantics.SOS
open Execution.Runtime (Value)

theorem fact {ctx : Context} {p : Program} {a b : State p.site} (rule : Ground ctx p.site a b) : Edge ctx p a b :=
  Derives.apply (R := (presentation ctx p).rules) (r := ⟨[], .step a b⟩) (.ground rule) (by simp)

theorem invoke {ctx : Context} {p : Program} {a b : DirectSequence.State p.site}
    (live : Live a) (edge : DirectSequence.Edge p a b) : Edge ctx p (.active a) (attach ctx b) :=
  Proofs.invoke live edge

theorem invoke_run {ctx : Context} {p : Program} {a b : DirectSequence.State p.site}
    (run : DirectSequence.Runs p a b) : Runs ctx p (attach ctx a) (attach ctx b) :=
  Proofs.invoke_run run

theorem closed {ctx : Context} {p : Program} (typed : ctx.Typed p) (program : DirectSequence.Typed p)
    (targets : p.site.body.TypedTargets) {a b : State p.site}
    (ready : Admitted ctx a) (edge : Edge ctx p a b) : Admitted ctx b :=
  Proofs.closed typed program targets ready edge

/-- From an invocation trap onward, execution only unwinds or discards pending operands and code. -/
theorem trap_bypasses {ctx : Context} {p : Program} {a b : State p.site}
    (trapped : Unwinding p.site a) (run : Runs ctx p a b) : Unwinding p.site b :=
  Proofs.trap_bypasses trapped run

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing
