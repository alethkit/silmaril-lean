module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness (Demand)
open Continuation (Stack)
open Continuation.Partial (ActivePrimitive Config Eval Site)
open Continuation.Partial.Executable
  (Actions next? observe run runFor observe_returned observe_blocked observe_suspended step_iff
    returns_iff_run blocks_iff_run)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {results : Ports (Ty V S)}
variable {actions : Actions m σ} {demand : Demand} {left right : Config m σ results}

theorem prefix_mono {small large : Nat} (le : small ≤ large)
    (h : PrefixMatches actions demand large left right) :
    PrefixMatches actions demand small left right := by
  induction small generalizing large left right with
  | zero => exact .cut _ _
  | succ small ih =>
    cases h with
    | cut => omega
    | returned matchOut => exact .returned matchOut
    | step stepL stepR later => exact .step stepL stepR (ih (Nat.le_of_succ_le_succ le) later)
    | blocked undefined resume =>
      exact .blocked undefined (fun v s => ih (Nat.le_of_succ_le_succ le) (resume v s))

/-- The shared continuation proof works at a finite observation budget or,
for code without feedback, with its original inductive settling judgment. -/
@[expose] def AtDepth (actions : Actions m σ) (demand : Demand) (depth : Option Nat)
    (left right : Config m σ results) : Prop :=
  match depth with
  | none => Matches actions demand left right
  | some n => PrefixMatches actions demand n left right

theorem depth_step {depth : Option Nat} {nextL nextR : Config m σ results}
    (stepL : next? actions left = some nextL) (stepR : next? actions right = some nextR)
    (later : AtDepth actions demand depth nextL nextR) : AtDepth actions demand depth left right := by
  cases depth with
  | none => exact Matches.step stepL stepR later
  | some n =>
    exact prefix_mono (Nat.le_succ n) (PrefixMatches.step stepL stepR later)

theorem depth_blocked {depth : Option Nat} {site : Site m} {left right : Stack m site.outs results}
    {store : σ} (undefined : (actions.step site.opcode site.input).run store = none)
    (resume : ∀ value nextStore, AtDepth actions demand depth
      ⟨.returned value left, nextStore⟩ ⟨.returned value right, nextStore⟩) :
    AtDepth actions demand depth ⟨.eval site.job left, store⟩ ⟨.eval site.job right, store⟩ := by
  cases depth with
  | none => exact Matches.blocked undefined resume
  | some n =>
    exact prefix_mono (Nat.le_succ n) (PrefixMatches.blocked undefined resume)

theorem sees_block {site : Site m} (frame : Stack m site.outs results) (store : σ)
    (undefined : (actions.step site.opcode site.input).run store = none) :
    observe actions ⟨.eval site.job frame, store⟩ = .blocked ⟨site, frame⟩ store := by
  apply observe_blocked.2
  refine ⟨rfl, rfl, ?_⟩
  change Part.ofOption ((actions.step site.opcode site.input).run store) = Part.none
  rw [undefined]
  rfl

private theorem stays (fuel : Nat) {source : Config m σ results} (stopped : next? actions source = none) :
    runFor actions fuel source = source := by
  cases fuel with
  | zero => rfl
  | succ n => simp only [runFor, stopped]

theorem prefix_observes (fuel after : Nat)
    (h : PrefixMatches actions demand (fuel + after + 1) left right) :
    PrefixObservationsAgree actions demand after
      (observe actions (runFor actions fuel left)) (observe actions (runFor actions fuel right)) := by
  induction fuel generalizing left right with
  | zero =>
    cases h with
    | returned related =>
      rw [runFor, runFor, observe_returned.2 rfl, observe_returned.2 rfl]
      exact .returned related
    | step stepL stepR _ =>
      rw [runFor, runFor, observe_suspended.2 ⟨_, step_iff.2 stepL⟩,
        observe_suspended.2 ⟨_, step_iff.2 stepR⟩]
      exact .suspended _ _
    | blocked undefined resume =>
      rw [runFor, runFor, sees_block _ _ undefined, sees_block _ _ undefined]
      exact .blocked (fun value store => prefix_mono (by omega) (resume value store))
  | succ fuel ih =>
    cases h with
    | returned related =>
      rw [stays _ rfl, stays _ rfl, observe_returned.2 rfl, observe_returned.2 rfl]
      exact .returned related
    | step stepL stepR later =>
      rw [runFor, stepL, runFor, stepR]
      apply ih
      exact prefix_mono (by omega) later
    | @blocked depth site left right store undefined resume =>
      have stopped (frame : Stack m site.outs results) : next? actions ⟨.eval site.job frame, store⟩ = none := by
        change ((actions.step site.opcode site.input).run store).map
          (fun (value, middle) => (⟨.returned value frame, middle⟩ : Config m σ results)) = none
        rw [undefined]
        rfl
      rw [stays _ (stopped left), stays _ (stopped right), sees_block _ _ undefined, sees_block _ _ undefined]
      exact .blocked (fun value middle => prefix_mono (by omega) (resume value middle))

theorem finite_return {jobL jobR : Job m results} {initial stopped : σ}
    {value : Tuple m.Val results}
    (matched : ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start jobL, initial⟩ ⟨Continuation.start jobR, initial⟩)
    (evaluated : Eval actions.toPrimitives jobL initial (.returned value stopped)) :
    ∃ other, Eval actions.toPrimitives jobR initial (.returned other stopped) ∧ demand.Agrees value other := by
  obtain ⟨fuel, ranL⟩ := returns_iff_run.1 evaluated
  have paired := prefix_observes fuel 0 (matched _)
  change PrefixObservationsAgree actions demand 0 (run actions fuel jobL initial) (run actions fuel jobR initial) at paired
  rw [ranL] at paired
  generalize ranR : run actions fuel jobR initial = out at paired
  cases paired with
  | returned agree => exact ⟨_, returns_iff_run.2 ⟨fuel, ranR⟩, agree⟩

theorem finite_block {jobL jobR : Job m results} {initial stopped : σ} {site : Site m}
    {pendingL : Continuation.Descent.Pending m site.outs results}
    (matched : ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start jobL, initial⟩ ⟨Continuation.start jobR, initial⟩)
    (evaluated : Eval actions.toPrimitives jobL initial (.blocked site pendingL stopped)) :
    ∃ pendingR, Eval actions.toPrimitives jobR initial (.blocked site pendingR stopped) ∧
      ∀ depth value store, PrefixMatches actions demand depth
        ⟨.returned value (pendingL.push .halt), store⟩ ⟨.returned value (pendingR.push .halt), store⟩ := by
  let activeL : ActivePrimitive m results := ⟨site, pendingL.push .halt⟩
  have seen : ∃ fuel, run actions fuel jobL initial = .blocked activeL stopped :=
    blocks_iff_run.1 ⟨pendingL, evaluated, rfl⟩
  obtain ⟨fuel, ranL⟩ := seen
  have paired := prefix_observes fuel 0 (matched _)
  change PrefixObservationsAgree actions demand 0 (run actions fuel jobL initial) (run actions fuel jobR initial) at paired
  rw [ranL] at paired
  dsimp only [activeL] at paired
  generalize ranR : run actions fuel jobR initial = out at paired
  cases paired with
  | @blocked _ _ frameR _ _ =>
    obtain ⟨pendingR, evaluation, stack⟩ := blocks_iff_run.2 ⟨fuel, ranR⟩
    refine ⟨pendingR, evaluation, ?_⟩
    intro depth value store
    have again := prefix_observes fuel depth (matched _)
    change PrefixObservationsAgree actions demand depth (run actions fuel jobL initial) (run actions fuel jobR initial) at again
    rw [ranL, ranR] at again
    dsimp only [activeL] at again
    cases again with
    | blocked resume =>
      change frameR = pendingR.push .halt at stack
      rw [← stack]
      exact resume value store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs
