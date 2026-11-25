module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs

open Silmaril.Semantics.SOS

inductive Move (call : Invocation) : State call → State call → Prop where
  | framed {a b} (edge : Framed.Edge call.context call.body.invocation a b) : Move call (.framed a) (.framed b)
  | ground {a b} (rule : Ground call a b) : Move call a b

theorem invert {call : Invocation} {a b : State call} (edge : Edge call a b) : Move call a b := by
  refine Derives.least (M := fun j => match j with
    | .body j => (Framed.presentation call.context call.body.invocation).Derives j
    | .step a b => Move call a b) edge ?_
  intro r rule ih
  change RuleInstance call r at rule
  cases rule with
  | inherit rule => exact Derives.apply rule (fun j mem => ih (.body j) (List.mem_map_of_mem mem))
  | framed a b => exact .framed (ih _ (List.Mem.head _))
  | ground rule => exact .ground rule

theorem framed {call : Invocation} {a b : Framed.State call.context call.body.invocation.site}
    (edge : Framed.Edge call.context call.body.invocation a b) : Edge call (.framed a) (.framed b) := by
  have inherited := Derives.map
    (R := (Framed.presentation call.context call.body.invocation).rules) (Q := (presentation call).rules)
    Judgment.body (fun _ rule => RuleInstance.inherit rule) edge
  exact Derives.apply (R := (presentation call).rules)
    (r := ⟨[.body (.step a b)], .step (.framed a) (.framed b)⟩) (.framed a b)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ inherited)

theorem framed_run {call : Invocation} {a b : Framed.State call.context call.body.invocation.site}
    (run : Framed.Runs call.context call.body.invocation a b) : Runs call (.framed a) (.framed b) :=
  Relation.ReflTransGen.lift State.framed (fun _ _ step => framed step) _ _ run

theorem closed {call : Invocation} (typed : Typed call) (program : DirectSequence.Typed call.body.invocation)
    (targets : call.body.invocation.site.body.TypedTargets) (suffix : call.context.sequence.TypedTargets)
    {a b : State call} (ready : Admitted a) (edge : Edge call a b) : Admitted b := by
  cases invert edge with
  | framed move => exact Framed.closed typed.continuation program targets suffix ready move
  | ground rule => cases rule <;> trivial

theorem run_iff {C : Type} {call : Invocation} (emit : State call → C) (native : C → C → Prop)
    (typed : Typed call) (program : DirectSequence.Typed call.body.invocation)
    (targets : call.body.invocation.site.body.TypedTargets) (suffix : call.context.sequence.TypedTargets)
    (sound : ∀ {a b}, Edge call a b → native (emit a) (emit b))
    (read : ∀ {a b}, Admitted a → native (emit a) b → ∃ out, Edge call a out ∧ b = emit out)
    {a : State call} {b : C} (ready : Admitted a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs call a out ∧ Admitted out ∧ b = emit out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨mid, path, admitted, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := read admitted step
      exact ⟨out, path.tail edge, closed typed program targets suffix admitted edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ edge => sound edge) _ _ path

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs
