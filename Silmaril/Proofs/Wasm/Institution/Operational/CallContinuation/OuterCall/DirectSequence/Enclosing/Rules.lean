module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs

open Silmaril.Semantics.SOS
open Execution.Runtime (Value)

inductive Move (ctx : Context) (p : Program) : State p.site → State p.site → Prop where
  | invoke {a b : DirectSequence.State p.site} (live : Live a) (step : DirectSequence.Edge p a b) :
      Move ctx p (.active a) (attach ctx b)
  | ground {a b : State p.site} (step : Ground ctx p.site a b) : Move ctx p a b

theorem invert {ctx : Context} {p : Program} {a b : State p.site} (edge : Edge ctx p a b) : Move ctx p a b := by
  refine Derives.least (M := fun j => match j with
    | .invocation j => (DirectSequence.presentation p).Derives j
    | .step a b => Move ctx p a b) edge ?_
  intro r rule ih
  change RuleInstance ctx p r at rule
  cases rule with
  | inherit rule => exact Derives.apply rule (fun j mem => ih (.invocation j) (List.mem_map_of_mem mem))
  | invoke b live => exact .invoke live (ih _ (List.Mem.head _))
  | ground rule => exact .ground rule

theorem invoke {ctx : Context} {p : Program} {a b : DirectSequence.State p.site}
    (live : Live a) (edge : DirectSequence.Edge p a b) : Edge ctx p (.active a) (attach ctx b) := by
  have inherited := Derives.map
    (R := (DirectSequence.presentation p).rules) (Q := (presentation ctx p).rules)
    Judgment.invocation (fun _ rule => RuleInstance.inherit rule) edge
  exact Derives.apply (R := (presentation ctx p).rules)
    (r := ⟨[.invocation (.step a b)], .step (.active a) (attach ctx b)⟩) (.invoke b live)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ inherited)

theorem invoke_run {ctx : Context} {p : Program} {a b : DirectSequence.State p.site}
    (run : DirectSequence.Runs p a b) : Runs ctx p (attach ctx a) (attach ctx b) := by
  refine Relation.ReflTransGen.lift (attach ctx) ?_ _ _ run
  intro before after step
  cases before with
  | done _ => exact (DirectSequence.done_no_edge step).elim
  | _ => exact invoke trivial step

theorem attached {ctx : Context} {p : Program} (typed : ctx.Typed p) {q : DirectSequence.State p.site}
    (ready : DirectSequence.Admitted p.site q) : Admitted ctx (attach ctx q) := by
  cases q with
  | call | invoke | label | exit => exact ⟨trivial, ready⟩
  | done result =>
    cases result with
    | trap => trivial
    | values stack =>
      change stack.map Value.type = p.site.result.toList at ready
      simpa [Context.Typed, Admitted, attach, Computed.Prefix.WellTyped, Computed.Prefix.stackTypes,
        List.map_append, List.reverse_append, ready] using typed

theorem closed {ctx : Context} {p : Program} (typed : ctx.Typed p) (program : DirectSequence.Typed p)
    (targets : p.site.body.TypedTargets) {a b : State p.site}
    (ready : Admitted ctx a) (edge : Edge ctx p a b) : Admitted ctx b := by
  cases invert edge with
  | invoke _ step => exact attached typed (DirectSequence.closed program targets ready.2 step)
  | ground rule =>
    cases rule with
    | discard => trivial
    | @resume stack op rest out step =>
      cases out with
      | trap => trivial
      | values => exact Computed.Prefix.preserve step ready

theorem trap_bypasses {ctx : Context} {p : Program} {a b : State p.site}
    (trapped : Unwinding p.site a) (run : Runs ctx p a b) : Unwinding p.site b := by
  induction run with
  | refl => exact trapped
  | tail _ edge ih =>
    cases ih with
    | active trapped live =>
      cases invert edge with
      | invoke _ move =>
        have stillTrapped := DirectSequence.trap_bypasses trapped (Relation.ReflTransGen.single move)
        cases stillTrapped with
        | label stack rest => exact .active (.label stack rest) trivial
        | exit => exact .active .exit trivial
        | done => exact .trapped ctx.saved ctx.continuation
      | ground rule => cases rule
    | trapped stack rest =>
      cases invert edge with
      | ground rule => cases rule; exact .trapped _ _

theorem run_iff {C : Type} {ctx : Context} {p : Program} (emit : State p.site → C) (native : C → C → Prop)
    (typed : ctx.Typed p) (program : DirectSequence.Typed p) (targets : p.site.body.TypedTargets)
    (sound : ∀ {a b}, Edge ctx p a b → native (emit a) (emit b))
    (read : ∀ {a b}, Admitted ctx a → native (emit a) b → ∃ out, Edge ctx p a out ∧ b = emit out)
    {a : State p.site} {b : C} (ready : Admitted ctx a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs ctx p a out ∧ Admitted ctx out ∧ b = emit out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨mid, path, admitted, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := read admitted step
      exact ⟨out, path.tail edge, closed typed program targets admitted edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ edge => sound edge) _ _ path

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs
