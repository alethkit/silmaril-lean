module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence

open Silmaril.Semantics.SOS
open StraightLine

theorem fact {p : Program} {a b : State p.site} (rule : Ground p a b) : Edge p a b :=
  Derives.apply (R := (presentation p).rules) (r := ⟨[], .step a b⟩) (.ground rule) (by simp)

theorem underLabel {p : Program} {a b : Sequence.State p.site.body}
    (edge : Sequence.Edge p.site.body a b) : Edge p (.label a) (.label b) :=
  Proofs.underLabel edge

theorem label_run {p : Program} {a b : Sequence.State p.site.body}
    (run : Sequence.Runs p.site.body a b) : Runs p (.label a) (.label b) :=
  Proofs.label_run run

/-- Once the outer body traps, the remaining steps only discard pending code and unwind. -/
theorem trap_bypasses {p : Program} {a b : State p.site}
    (trap : Unwinding p.site a) (run : Runs p a b) : Unwinding p.site b :=
  Proofs.trap_bypasses trap run

theorem closed {p : Program} (typed : Typed p) (targets : p.site.body.TypedTargets)
    {a b : State p.site} (ready : Admitted p.site a) (edge : Edge p a b) : Admitted p.site b :=
  Proofs.closed typed targets ready edge

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence
