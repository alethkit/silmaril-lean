module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing

open StraightLine
open Execution.Runtime (Value)

theorem resume {ctx : Context} {p : Program} {a b : Sequence.State ctx.sequence}
    (edge : Sequence.Edge ctx.sequence a b) : Edge ctx p (.continuation a) (.continuation b) :=
  Proofs.resume edge

theorem resume_run {ctx : Context} {p : Program} {a b : Sequence.State ctx.sequence}
    (run : Sequence.Runs ctx.sequence a b) : Runs ctx p (.continuation a) (.continuation b) :=
  Proofs.resume_run run

theorem numeric_typed_iff {p : Program} (frame : Execution.Runtime.Frame)
    (saved : List Value) (code : List Computed.Prefix.Op) (results : List NumType) :
    (Context.numeric frame saved code results).Typed p ↔
      Computed.Prefix.check (frame.locals.map Value.type)
        (p.site.result.toList.reverse ++ Computed.Prefix.stackTypes saved) code = some results.reverse :=
  Proofs.numeric_typed_iff frame saved code results

theorem invoke {ctx : Context} {p : Program} {a b : DirectSequence.State p.site}
    (live : Live a) (edge : DirectSequence.Edge p a b) : Edge ctx p (.active a) (attach ctx b) :=
  Proofs.invoke live edge

theorem invoke_run {ctx : Context} {p : Program} {a b : DirectSequence.State p.site}
    (run : DirectSequence.Runs p a b) : Runs ctx p (attach ctx a) (attach ctx b) :=
  Proofs.invoke_run run

theorem closed {ctx : Context} {p : Program} (typed : ctx.Typed p) (program : DirectSequence.Typed p)
    (targets : p.site.body.TypedTargets) (suffix : ctx.sequence.TypedTargets) {a b : State ctx p.site}
    (ready : Admitted a) (edge : Edge ctx p a b) : Admitted b :=
  Proofs.closed typed program targets suffix ready edge

/-- From an invocation trap onward, execution only unwinds or discards pending operands and code. -/
theorem trap_bypasses {ctx : Context} {p : Program} {a b : State ctx p.site}
    (trapped : Unwinding ctx p.site a) (run : Runs ctx p a b) : Unwinding ctx p.site b :=
  Proofs.trap_bypasses trapped run

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing
