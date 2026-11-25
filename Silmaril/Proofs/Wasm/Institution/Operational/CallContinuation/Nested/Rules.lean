module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs

open Silmaril.Semantics.SOS

inductive Move (fn : CallFrame.Callee) (arity : Nat) : State → State → Prop where
  | context {a b : CallContinuation.State} (inner : CallContinuation.Edge fn a b) :
      Move fn arity (.label a) (.label b)
  | ground {a b : State} (rule : Ground arity a b) : Move fn arity a b

theorem invert {fn : CallFrame.Callee} {arity : Nat} {a b : State} (edge : Edge fn arity a b) : Move fn arity a b := by
  refine Derives.least (M := fun j => match j with
    | .body j => (CallContinuation.presentation fn).Derives j
    | .step a b => Move fn arity a b) edge ?_
  intro r hr ih
  change RuleInstance fn arity r at hr
  cases hr with
  | @body r rule => exact .apply rule (fun j hj => ih (.body j) (List.mem_map_of_mem hj))
  | context a b => exact .context (ih _ (List.Mem.head _))
  | ground rule => exact .ground rule

private theorem body_derives (fn : CallFrame.Callee) (arity : Nat) {j : CallContinuation.Judgment}
    (edge : (CallContinuation.presentation fn).Derives j) :
    (presentation fn arity).Derives (.body j) := by
  refine Derives.least (M := fun j => (presentation fn arity).Derives (.body j)) edge ?_
  intro r rule ih
  change CallContinuation.RuleInstance fn r at rule
  refine Derives.apply (R := (presentation fn arity).rules)
    (r := ⟨r.premises.map Judgment.body, .body r.conclusion⟩) (.body rule) ?_
  intro j hj
  change j ∈ r.premises.map Judgment.body at hj
  obtain ⟨before, mem, rfl⟩ := List.mem_map.mp hj
  exact ih before mem

theorem underLabel {fn : CallFrame.Callee} {arity : Nat} {a b : CallContinuation.State}
    (inner : CallContinuation.Edge fn a b) : Edge fn arity (.label a) (.label b) :=
  Derives.apply (R := (presentation fn arity).rules)
    (r := ⟨[.body (.outer a b)], .step (.label a) (.label b)⟩) (.context a b)
    (fun _ h => (List.mem_singleton.mp h).symm ▸ body_derives fn arity inner)

theorem closed {fn : CallFrame.Callee} {arity : Nat} {a b : State}
    (guard : Admitted fn a) (edge : Edge fn arity a b) : Admitted fn b := by
  cases invert edge with
  | context inner => exact CallContinuation.closed guard inner
  | ground rule => cases rule <;> trivial

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop) {fn : CallFrame.Callee} {arity : Nat}
    (sound : ∀ {a b}, Edge fn arity a b → native (emit a) (emit b))
    (readback : ∀ {a b}, Admitted fn a → native (emit a) b → ∃ out, Edge fn arity a out ∧ b = emit out)
    {a : State} {b : C} (guard : Admitted fn a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs fn arity a out ∧ Admitted fn out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, guard, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, typed, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback typed step
      exact ⟨out, path.tail edge, closed typed edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ e => sound e) _ _ path

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs
