module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs

open Silmaril.Semantics.SOS

inductive Move (site : CallSite) : State → State → Prop where
  | ground {a b} (rule : Ground site a b) : Move site a b
  | nest {a b} (rule : Nested.Edge site.callee.inner site.callee.arity a b) :
      Move site (.nested a) (.nested b)

theorem invert {site : CallSite} {a b : State} (edge : Edge site a b) : Move site a b := by
  refine Derives.least (M := fun j => match j with
    | .nested j => (Nested.presentation site.callee.inner site.callee.arity).Derives j
    | .transition a b => Move site a b) edge ?_
  intro r rule ih
  change RuleInstance site r at rule
  cases rule with
  | @inherit r h => exact Derives.apply h (fun j mem => ih (.nested j) (List.mem_map_of_mem mem))
  | delegate a b => exact .nest (ih _ (List.Mem.head _))
  | ground h => exact .ground h

theorem delegate {site : CallSite} {a b : Nested.State}
    (inner : Nested.Edge site.callee.inner site.callee.arity a b) : Edge site (.nested a) (.nested b) := by
  have h := Derives.map
    (R := (Nested.presentation site.callee.inner site.callee.arity).rules) (Q := (presentation site).rules)
    Judgment.nested (fun _ rule => RuleInstance.inherit rule) inner
  exact Derives.apply (R := (presentation site).rules)
    (r := ⟨[.nested (.step a b)], .transition (.nested a) (.nested b)⟩) (.delegate a b)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ h)

theorem closed {site : CallSite} (typed : Typed site) {a b : State}
    (admitted : Admitted site a) (edge : Edge site a b) : Admitted site b := by
  cases invert edge with
  | ground rule =>
    cases rule with
    | resolve | enter => trivial
    | resolveInner => exact ⟨trivial, typed.innerArgs, typed.body⟩
  | nest e => exact Nested.closed admitted e

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop)
    {site : CallSite} (g : Typed site)
    (sound : ∀ {a b}, Edge site a b → native (emit a) (emit b))
    (step : ∀ {a b}, Admitted site a →
      (native (emit a) b ↔ ∃ out, Edge site a out ∧ b = emit out))
    {a : State} {b : C} (valid : Admitted site a) :
    Relation.ReflTransGen native (emit a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = emit out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, valid, rfl⟩
    | tail _ h ih =>
      obtain ⟨mid, path, ready, rfl⟩ := ih
      obtain ⟨out, e, rfl⟩ := (step ready).mp h
      exact ⟨out, path.tail e, closed g ready e, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ e => sound e) _ _ path

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs
