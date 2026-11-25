module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed

open Silmaril.Semantics.SOS

theorem fact {site : Site} {a b : State} (rule : Ground site a b) : Edge site a b :=
  Derives.apply (R := (presentation site).rules) (r := ⟨[], .step a b⟩)
    (.ground rule) (by simp)

theorem delegate {site : Site} {a b : StraightLine.State}
    (rule : StraightLine.Edge site.innerSite a b) : Edge site (.inner a) (.inner b) :=
  Proofs.delegate rule

theorem closed {site : Site} (typed : Typed site) {a b : State}
    (admitted : Admitted site a) (edge : Edge site a b) : Admitted site b :=
  Proofs.closed typed admitted edge

theorem inner_runs_iff {site : Site} {a : StraightLine.State} {b : State} :
    Runs site (.inner a) b ↔ ∃ out, StraightLine.Runs site.innerSite a out ∧ b = .inner out :=
  Proofs.inner_runs_iff

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed
