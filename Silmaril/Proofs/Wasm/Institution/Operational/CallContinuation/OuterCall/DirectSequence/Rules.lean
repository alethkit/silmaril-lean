module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs

open Silmaril.Semantics.SOS
open StraightLine
open Execution.Runtime (Value)

inductive Move (p : Program) : State p.site → State p.site → Prop where
  | body {a b} (step : Sequence.Edge p.site.body a b) : Move p (.label a) (.label b)
  | ground {a b} (step : Ground p a b) : Move p a b

theorem invert {p : Program} {a b : State p.site} (edge : Edge p a b) : Move p a b := by
  refine Derives.least (M := fun j => match j with
    | .body j => (Sequence.presentation p.site.body).Derives j
    | .step a b => Move p a b) edge ?_
  intro r rule ih
  change RuleInstance p r at rule
  cases rule with
  | inherit rule => exact Derives.apply rule (fun j mem => ih (.body j) (List.mem_map_of_mem mem))
  | underLabel a b => exact .body (ih _ (List.Mem.head _))
  | ground rule => exact .ground rule

theorem done_no_edge {p : Program} {result : Nested.Result} {b : State p.site} :
    ¬ Edge p (.done result) b := by
  intro edge
  cases invert edge with
  | ground rule => cases rule

theorem underLabel {p : Program} {a b : Sequence.State p.site.body}
    (edge : Sequence.Edge p.site.body a b) : Edge p (.label a) (.label b) := by
  have lifted := Derives.map
    (R := (Sequence.presentation p.site.body).rules) (Q := (presentation p).rules)
    Judgment.body (fun _ rule => RuleInstance.inherit rule) edge
  exact Derives.apply (R := (presentation p).rules)
    (r := ⟨[.body (.step a b)], .step (.label a) (.label b)⟩) (.underLabel a b)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ lifted)

theorem label_run {p : Program} {a b : Sequence.State p.site.body}
    (run : Sequence.Runs p.site.body a b) : Runs p (.label a) (.label b) :=
  Relation.ReflTransGen.lift State.label (fun _ _ e => underLabel e) _ _ run

theorem trap_bypasses {p : Program} {a b : State p.site}
    (trap : Unwinding p.site a) (run : Runs p a b) : Unwinding p.site b := by
  induction run with
  | refl => exact trap
  | tail _ edge ih =>
    cases ih with
    | label stack rest =>
      cases invert edge with
      | body move =>
        obtain ⟨kept, pending, rfl⟩ := Sequence.trap_bypasses (Relation.ReflTransGen.single move)
        exact .label kept pending
      | ground rule =>
        cases rule with
        | leaveLabel finished => cases finished; exact .exit
    | exit =>
      cases invert edge with
      | ground rule => cases rule; exact .done
    | done =>
      cases invert edge with
      | ground rule => cases rule

theorem closed {p : Program} (typed : Typed p) (targets : p.site.body.TypedTargets)
    {a b : State p.site} (ready : Admitted p.site a) (edge : Edge p a b) : Admitted p.site b := by
  cases invert edge with
  | body step => exact Sequence.closed targets ready step
  | ground step =>
    cases step with
    | resolve => trivial
    | enter => exact typed.body
    | leaveFrame => exact ready
    | leaveLabel finished =>
      cases finished with
      | trap => trivial
      | values stack =>
        change some (OuterCall.Computed.Prefix.stackTypes stack) = some p.site.result.toList.reverse at ready
        exact List.reverse_injective (Option.some.inj ready)

theorem result_arity {site : Site} {result : Nested.Result} (typed : ResultTyped site result) :
    ResultArity site result := by
  cases result with
  | values stack =>
    change stack.map Value.type = site.result.toList at typed
    simpa [ResultArity, Site.arity] using congrArg List.length typed
  | trap => trivial

theorem run_iff {C : Type} {p : Program} (emit : State p.site → C) (native : C → C → Prop)
    (typed : Typed p) (targets : p.site.body.TypedTargets)
    (sound : ∀ {a b}, Edge p a b → native (emit a) (emit b))
    (read : ∀ {a b}, Admitted p.site a → native (emit a) b → ∃ out, Edge p a out ∧ b = emit out)
    {a : State p.site} {b : C} (ready : Admitted p.site a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs p a out ∧ Admitted p.site out ∧ b = emit out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨mid, path, admitted, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := read admitted step
      exact ⟨out, path.tail edge, closed typed targets admitted edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ edge => sound edge) _ _ path

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs
