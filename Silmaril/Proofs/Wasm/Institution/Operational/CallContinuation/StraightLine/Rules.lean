module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs

open Silmaril.Semantics.SOS
open Execution.Runtime (Value)
open OuterCall.Computed

inductive Move (site : Site) : State → State → Prop where
  | ground {a b} (rule : Ground site a b) : Move site a b
  | call {a b : CallFrame.State} (live : Active a) (edge : CallFrame.Edge site.callee a b) :
      Move site (.active a) (attach site b)

theorem invert {site : Site} {a b : State} (edge : Edge site a b) : Move site a b := by
  refine Derives.least (M := fun j => match j with
    | .inner j => (CallFrame.presentation site.callee).Derives j
    | .step a b => Move site a b) edge ?_
  intro r rule ih
  change RuleInstance site r at rule
  cases rule with
  | @inner r h => exact Derives.apply h (fun j mem => ih (.inner j) (List.mem_map_of_mem mem))
  | call a b live => exact .call live (ih _ (List.Mem.head _))
  | ground h => exact .ground h

theorem call {site : Site} {a b : CallFrame.State} (live : Active a)
    (edge : CallFrame.Edge site.callee a b) : Edge site (.active a) (attach site b) := by
  have h := Derives.map
    (R := (CallFrame.presentation site.callee).rules) (Q := (presentation site).rules)
    Judgment.inner (fun _ rule => RuleInstance.inner rule) edge
  exact Derives.apply (R := (presentation site).rules)
    (r := ⟨[.inner (.call a b)], .step (.active a) (attach site b)⟩) (.call a b live)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ h)

private theorem resumed_typed {site : Site} {stack : List Value} {rest : List Prefix.Op}
    (typed : Prefix.WellTyped site.outer.locals stack rest site.result.toList) :
    Admitted site (resumed stack rest) := by
  cases rest with
  | nil => exact Prefix.nil_iff.mp typed
  | cons => exact ⟨List.cons_ne_nil _ _, typed⟩

private theorem trapped_typed (site : Site) (stack : List Value) (rest : List Prefix.Op) :
    Admitted site (trapped stack rest) := by
  cases stack <;> cases rest <;> simp [trapped, Admitted, BoundaryTyped]

private theorem attached_typed {site : Site} {a b : CallFrame.State}
    (ready : Active a ∧ CallFrame.Admitted site.callee a ∧ site.ResumeTyped a.saved)
    (edge : CallFrame.Edge site.callee a b) : Admitted site (attach site b) := by
  have typed := CallFrame.closed ready.2.1 edge
  have kept := CallFrame.saved_of_live edge (by
    intro xs eq
    rw [eq] at ready
    exact ready.1)
  have continuation : site.ResumeTyped b.saved := kept.symm ▸ ready.2.2
  cases b with
  | invoke | label | exit => exact ⟨trivial, typed, continuation⟩
  | trapped saved => exact trapped_typed site saved site.continuation
  | returned saved results =>
    apply resumed_typed
    change (results.map Value.type).reverse = site.callee.result.toList at typed
    simpa [Site.ResumeTyped, CallFrame.State.saved, Prefix.WellTyped, Prefix.stackTypes,
      List.map_append, List.reverse_append, typed] using continuation

theorem closed {site : Site} {a b : State} (ready : Admitted site a)
    (edge : Edge site a b) : Admitted site b := by
  cases invert edge with
  | call _ inner => exact attached_typed ready inner
  | ground ground =>
    cases ground with
    | resolve => exact ⟨trivial, ready⟩
    | @resume stack op rest ans step =>
      cases ans with
      | values => exact resumed_typed (Prefix.preserve step ready.2)
      | trap saved => exact trapped_typed site saved rest
    | discard => exact trapped_typed ..
    | boundary rule => cases rule <;> exact ready

private theorem unwinding_closed {site : Site} {a b : State}
    (ready : Unwinding a) (edge : Edge site a b) : Unwinding b := by
  cases invert edge with
  | call => exact ready.elim
  | ground rule =>
    cases rule with
    | resolve | resume => exact ready.elim
    | @discard stack kept before rest move =>
      cases kept <;> cases rest <;> trivial
    | boundary rule => cases rule <;> exact ready

theorem callee_trap_bypasses {site : Site} {saved : List Value} {a : State}
    (run : Runs site (attach site (.trapped saved)) a) : Unwinding a := by
  induction run with
  | refl =>
    change Unwinding (trapped saved site.continuation)
    generalize site.continuation = rest
    cases saved <;> cases rest <;> trivial
  | tail _ step ih => exact unwinding_closed ih step

theorem nested_ready {site : Site} {phase : Nested.State}
    (ready : BoundaryTyped site.result.toList phase) : Nested.Admitted site.callee phase := by
  cases phase with
  | exit | done => trivial
  | label q =>
    cases q with
    | active | resume => exact ready.elim
    | done | trapped => trivial

private theorem isolated_trap_stuck {b : CallContinuation.State}
    (ground : CallContinuation.Ground (.trapped [] false) b) : False := by
  generalize eq : CallContinuation.State.trapped [] false = a at ground
  cases ground with
  | discardValues _ _ _ nz =>
    exact nz (List.append_eq_nil_iff.mp (CallContinuation.State.trapped.inj eq).1.symm).2
  | resume => cases eq
  | discardTail => exact Bool.noConfusion (CallContinuation.State.trapped.inj eq).2

theorem boundary_ground {site : Site} {a b : Nested.State}
    (ready : BoundaryTyped site.result.toList a) (edge : Nested.Edge site.callee site.arity a b) :
    Nested.Ground site.arity a b := by
  cases Nested.Proofs.invert edge with
  | ground h => exact h
  | @context a b h =>
    cases a with
    | active | resume => exact ready.elim
    | done =>
      cases CallContinuation.Proofs.invert h with
      | ground rule => cases rule
    | trapped saved keep =>
      cases saved with
      | cons => exact ready.elim
      | nil =>
        cases keep with
        | true => exact ready.elim
        | false =>
          cases CallContinuation.Proofs.invert h with
          | ground rule => exact (isolated_trap_stuck rule).elim

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop) {site : Site}
    (sound : ∀ {a b}, Edge site a b → native (emit a) (emit b))
    (readback : ∀ {a b}, Admitted site a → native (emit a) b → ∃ out, Edge site a out ∧ b = emit out)
    {a : State} {b : C} (ready : Admitted site a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs site a out ∧ Admitted site out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, admitted, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback admitted step
      exact ⟨out, path.tail edge, closed admitted edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ e => sound e) _ _ path

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs
