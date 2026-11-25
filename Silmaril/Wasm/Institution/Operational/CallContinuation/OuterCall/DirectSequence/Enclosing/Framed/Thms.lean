module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed

open Silmaril.Semantics.SOS
open StraightLine

theorem fact {ctx : Context} {p : Program} {a b : State ctx p.site} (rule : Ground ctx p.site a b) : Edge ctx p a b :=
  Derives.apply (R := (presentation ctx p).rules) (r := ⟨[], .step a b⟩) (.ground rule) (by simp)

theorem underLabel {ctx : Context} {p : Program} {a b : Enclosing.State ctx p.site}
    (step : Enclosing.Edge ctx p a b) : Edge ctx p (.label a) (.label b) :=
  Proofs.underLabel step

theorem label_run {ctx : Context} {p : Program} {a b : Enclosing.State ctx p.site}
    (run : Enclosing.Runs ctx p a b) : Runs ctx p (.label a) (.label b) :=
  Proofs.label_run run

/-- Lift a completed body run through the enclosing function's label and frame. -/
theorem finish_run {ctx : Context} {p : Program} {a : Enclosing.State ctx p.site}
    {q : Sequence.State ctx.sequence} {r : Nested.Result}
    (run : Enclosing.Runs ctx p a (.continuation q)) (finished : Sequence.Finished ctx.sequence q r)
    (arity : Sequence.ResultArity ctx.sequence r) : Runs ctx p (.label a) (.done r) :=
  ((label_run run).tail (fact (.leaveLabel finished))).tail (fact (.leaveFrame r arity))

theorem closed {ctx : Context} {p : Program} (typed : ctx.Typed p) (program : DirectSequence.Typed p)
    (targets : p.site.body.TypedTargets) (suffix : ctx.sequence.TypedTargets) {a b : State ctx p.site}
    (ready : Admitted a) (step : Edge ctx p a b) : Admitted b :=
  Proofs.closed typed program targets suffix ready step

theorem trap_unwinds {ctx : Context} {p : Program} {a b : State ctx p.site}
    (trap : Unwinding ctx p.site a) (run : Runs ctx p a b) : Unwinding ctx p.site b :=
  Proofs.trap_unwinds trap run

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed
