module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs

open Silmaril.Semantics.SOS

inductive Move (site : Site) : State → State → Prop where
  | ground {a b} (rule : Ground site a b) : Move site a b
  | callInner {a b} (rule : StraightLine.Edge site.innerSite a b) :
      Move site (.inner a) (.inner b)

theorem invert {site : Site} {a b : State} (edge : Edge site a b) : Move site a b := by
  refine Derives.least (M := fun j => match j with
    | .inner j => (StraightLine.presentation site.innerSite).Derives j
    | .step a b => Move site a b) edge ?_
  intro r rule ih
  change RuleInstance site r at rule
  cases rule with
  | @inherit r h => exact Derives.apply h (fun j mem => ih (.inner j) (List.mem_map_of_mem mem))
  | delegate a b => exact .callInner (ih _ (List.Mem.head _))
  | ground h => exact .ground h

theorem delegate {site : Site} {a b : StraightLine.State}
    (inner : StraightLine.Edge site.innerSite a b) : Edge site (.inner a) (.inner b) := by
  have h := Derives.map
    (R := (StraightLine.presentation site.innerSite).rules) (Q := (presentation site).rules)
    Judgment.inner (fun _ rule => RuleInstance.inherit rule) inner
  exact Derives.apply (R := (presentation site).rules)
    (r := ⟨[.inner (.step a b)], .step (.inner a) (.inner b)⟩) (.delegate a b)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ h)

private theorem evaluating_typed {site : Site} (typed : Typed site)
    {stack : List Execution.Runtime.Value} {rest : List Prefix.Op}
    (checked : Prefix.WellTyped site.toSite.frame.locals stack rest site.inner.params) :
    Admitted site (evaluating stack rest) := by
  cases rest with
  | nil => exact ⟨⟨Prefix.nil_iff.mp checked, typed.innerBody⟩, typed.continuationTyped⟩
  | cons => exact ⟨List.cons_ne_nil _ _, checked⟩

theorem closed {site : Site} (typed : Typed site) {a b : State}
    (admitted : Admitted site a) (edge : Edge site a b) : Admitted site b := by
  cases invert edge with
  | ground rule =>
    cases rule with
    | resolve => trivial
    | enter => exact evaluating_typed typed typed.prefixTyped
    | @evaluate stack op remaining out step =>
      cases out with
      | values => exact evaluating_typed typed (Prefix.preserve step admitted.2)
      | trap => exact .inr (by simp [Site.pending])
    | @discard stack kept before remaining step =>
      cases kept <;> cases remaining <;>
        simp [argumentTrap, Admitted, StraightLine.trapped, StraightLine.Admitted, StraightLine.BoundaryTyped]
  | callInner e => exact StraightLine.closed admitted e

theorem inner_runs_iff {site : Site} {a : StraightLine.State} {b : State} :
    Runs site (.inner a) b ↔ ∃ out, StraightLine.Runs site.innerSite a out ∧ b = .inner out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, rfl⟩
    | tail _ step ih =>
      obtain ⟨_, path, rfl⟩ := ih
      cases invert step with
      | callInner move => exact ⟨_, path.tail move, rfl⟩
      | ground rule => cases rule
  · rintro ⟨out, path, rfl⟩
    exact Relation.ReflTransGen.lift State.inner (fun _ _ e => delegate e) _ _ path

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

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs
