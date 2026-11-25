module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs

open Silmaril.Semantics.SOS

inductive Move (fn : CallFrame.Callee) : State → State → Prop where
  | call {a b : CallFrame.State} (live : Active a) (inner : CallFrame.Edge fn a b) :
      Move fn (.active a) (attach b)
  | ground {a b : State} (rule : Ground a b) : Move fn a b

theorem invert {fn : CallFrame.Callee} {a b : State} (edge : Edge fn a b) : Move fn a b := by
  refine Derives.least (M := fun j => match j with
    | .inner j => (CallFrame.presentation fn).Derives j
    | .outer a b => Move fn a b) edge ?_
  intro r hr ih
  change RuleInstance fn r at hr
  cases hr with
  | @inner r rule => exact .apply rule (fun j hj => ih (.inner j) (List.mem_map_of_mem hj))
  | call a b live => exact .call live (ih _ (List.Mem.head _))
  | ground rule => exact .ground rule

private theorem inner_derives (fn : CallFrame.Callee) {j : CallFrame.Judgment}
    (edge : (CallFrame.presentation fn).Derives j) : (presentation fn).Derives (.inner j) := by
  refine Derives.least (M := fun j => (presentation fn).Derives (.inner j)) edge ?_
  intro r rule ih
  change CallFrame.RuleInstance fn r at rule
  refine Derives.apply (R := (presentation fn).rules)
    (r := ⟨r.premises.map Judgment.inner, .inner r.conclusion⟩) (.inner rule) ?_
  intro j hj
  change j ∈ r.premises.map Judgment.inner at hj
  obtain ⟨before, mem, rfl⟩ := List.mem_map.mp hj
  exact ih before mem

theorem call {fn : CallFrame.Callee} {a b : CallFrame.State} (live : Active a)
    (inner : CallFrame.Edge fn a b) : Edge fn (.active a) (attach b) :=
  Derives.apply (R := (presentation fn).rules)
    (r := ⟨[.inner (.call a b)], .outer (.active a) (attach b)⟩) (.call a b live)
    (fun _ h => (List.mem_singleton.mp h).symm ▸ inner_derives fn inner)

theorem closed {fn : CallFrame.Callee} {a b : State} (guard : Admitted fn a) (edge : Edge fn a b) :
    Admitted fn b := by
  cases invert edge with
  | call live inner =>
    have typed := CallFrame.closed guard.2 inner
    rename_i a b
    cases b <;> first | exact ⟨trivial, typed⟩ | trivial
  | ground rule => cases rule <;> trivial

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop) {fn : CallFrame.Callee}
    (sound : ∀ {a b}, Edge fn a b → native (emit a) (emit b))
    (readback : ∀ {a b}, Admitted fn a → native (emit a) b → ∃ out, Edge fn a out ∧ b = emit out)
    {a : State} {b : C} (guard : Admitted fn a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs fn a out ∧ Admitted fn out ∧ b = emit out := by
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

end Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs
