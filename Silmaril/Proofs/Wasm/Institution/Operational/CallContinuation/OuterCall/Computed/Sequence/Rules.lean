module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Proofs

open Silmaril.Semantics.SOS

inductive Move (site : Site) : State → State → Prop where
  | ground {a b} (rule : Ground site a b) : Move site a b
  | nest {a b} (rule : Nested.Edge site.inner site.arity a b) :
      Move site (.nested a) (.nested b)

theorem invert {site : Site} {a b : State} (edge : Edge site a b) : Move site a b := by
  refine Derives.least (M := fun j => match j with
    | .nested j => (Nested.presentation site.inner site.arity).Derives j
    | .step a b => Move site a b) edge ?_
  intro r rule ih
  change RuleInstance site r at rule
  cases rule with
  | @inherit r h => exact Derives.apply h (fun j mem => ih (.nested j) (List.mem_map_of_mem mem))
  | delegate a b => exact .nest (ih _ (List.Mem.head _))
  | ground h => exact .ground h

theorem delegate {site : Site} {a b : Nested.State}
    (inner : Nested.Edge site.inner site.arity a b) : Edge site (.nested a) (.nested b) := by
  have h := Derives.map
    (R := (Nested.presentation site.inner site.arity).rules) (Q := (presentation site).rules)
    Judgment.nested (fun _ rule => RuleInstance.inherit rule) inner
  exact Derives.apply (R := (presentation site).rules)
    (r := ⟨[.nested (.step a b)], .step (.nested a) (.nested b)⟩) (.delegate a b)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ h)

theorem closed {site : Site} (typed : Typed site) {a b : State}
    (admitted : Admitted site a) (edge : Edge site a b) : Admitted site b := by
  cases invert edge with
  | ground rule =>
    cases rule with
    | resolve => trivial
    | enter => exact typed.prefixTyped
    | arg h => exact Prefix.preserve h admitted
    | trap => exact .inr (by simp [pending])
    | discard =>
      rename_i kept _ rest _
      cases kept <;> cases rest <;> simp [trapState, poppedTrap, Admitted, Nested.Admitted, CallContinuation.Admitted]
    | resolveInner => exact ⟨trivial, Prefix.nil_iff.mp admitted, typed.innerBody⟩
  | nest e => exact Nested.closed admitted e

theorem run_iff {C : Type} {site : Site} (emit : State → C) (native : C → C → Prop)
     (g : Typed site)
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

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Proofs
