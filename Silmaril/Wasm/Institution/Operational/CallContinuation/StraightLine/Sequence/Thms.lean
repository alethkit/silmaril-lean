module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence

open Silmaril.Semantics.SOS
open Execution.Runtime (Value)
open OuterCall.Computed

theorem fact {site : Site} {a b : State site} (rule : Ground site a b) : Edge site a b :=
  Derives.apply (R := (presentation site).rules) (r := ⟨[], .step a b⟩) (.ground rule) (by simp)

theorem call {site : Site} {i : site.TargetId} {a b : CallFrame.State} {rest : List (Op site)}
    (live : Active a) (edge : CallFrame.Edge (site.target i).callee a b) :
    Edge site (.active i a rest) (attach i rest b) :=
  Proofs.call live edge

theorem check_append (site : Site) (types : List NumType) (before after : List (Op site)) :
    check site types (before ++ after) = (check site types before).bind (fun next => check site next after) :=
  Proofs.check_append site types before after

theorem check_numeric (site : Site) (types : List NumType) (code : List Prefix.Op) :
    check site types (code.map .numeric) = Prefix.check (site.frame.locals.map Value.type) types code :=
  Proofs.check_numeric site types code

theorem closed {site : Site} (guard : site.TypedTargets) {a b : State site}
    (ready : Admitted site a) (edge : Edge site a b) : Admitted site b :=
  Proofs.closed guard ready edge

/-- Every finite run after a trap only unwinds. Pending calls cannot be entered. -/
theorem trap_bypasses {site : Site} {stack : List Value} {rest : List (Op site)} {b : State site}
    (run : Runs site (.trapped stack rest) b) : ∃ kept remaining, b = .trapped kept remaining :=
  Proofs.trap_bypasses run

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence
