module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
import Silmaril.Foundations.InfiniteTrace.Deterministic

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Proofs

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {actions : Actions m σ} {source target : Config m σ final}

theorem next_eq (actions : Actions m σ) (source : Config m σ final) :
    source.next actions.toPrimitives = _root_.Part.ofOption (next? actions source) := by
  cases selected : selectedPrimitive source.control with
  | none => simp only [Config.next, next?, selected]
  | some active =>
    simp only [Config.next, next?, selected]
    change (_root_.Part.ofOption ((actions.step active.site.opcode active.site.input).run source.store)).map _ =
      _root_.Part.ofOption (((actions.step active.site.opcode active.site.input).run source.store).map _)
    cases ran : (actions.step active.site.opcode active.site.input).run source.store <;> simp [_root_.Part.ofOption]

theorem step_iff : Step actions.toPrimitives source target ↔ next? actions source = some target := by
  unfold Step
  rw [next_eq, _root_.Part.mem_ofOption]
  rfl

private theorem stopped (actions : Actions m σ) (source : Config m σ final)
    (last : next? actions source = none) (fuel : Nat) : runFor actions fuel source = source := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [runFor, last]

theorem runFor_add (actions : Actions m σ) (first more : Nat) (source : Config m σ final) :
    runFor actions (first + more) source = runFor actions more (runFor actions first source) := by
  induction first generalizing source with
  | zero => simp only [Nat.zero_add, runFor]
  | succ first ih =>
    cases edge : next? actions source with
    | none => rw [stopped actions source edge, stopped actions source edge, stopped actions source edge]
    | some target => rw [Nat.succ_add]; simp only [runFor, edge, ih]

theorem runFor_reachable (actions : Actions m σ) (fuel : Nat) (source : Config m σ final) :
    ReflTransGen (Step actions.toPrimitives) source (runFor actions fuel source) := by
  induction fuel generalizing source with
  | zero => exact .refl
  | succ fuel ih =>
    cases edge : next? actions source with
    | none => simpa only [runFor, edge] using (ReflTransGen.refl (r := Step actions.toPrimitives) (a := source))
    | some target =>
      simpa only [runFor, edge] using (ih target).head (step_iff.mpr edge)

theorem reachable_iff :
    ReflTransGen (Step actions.toPrimitives) source target ↔ ∃ fuel, runFor actions fuel source = target := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨0, rfl⟩
    | tail _ edge ih =>
      obtain ⟨fuel, reached⟩ := ih
      exact ⟨fuel + 1, by rw [runFor_add, reached]; simp only [runFor, step_iff.mp edge]⟩
  · rintro ⟨fuel, rfl⟩
    exact runFor_reachable actions fuel source

private theorem result_iff {values : Tuple m.Val final} {store : σ} :
    source.result = some (values, store) ↔ source = ⟨.returned values .halt, store⟩ := by
  constructor
  · intro equal
    cases source with
    | mk state current =>
      cases state with
      | eval => cases equal
      | returned value stack =>
        cases stack with
        | halt =>
          change some (value, current) = some (values, store) at equal
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj equal)
          rfl
        | resume => cases equal
        | loop => cases equal
  · rintro rfl
    rfl

theorem observe_returned {values : Tuple m.Val final} {store : σ} :
    observe actions source = .returned values store ↔ source = ⟨.returned values .halt, store⟩ := by
  rw [← result_iff]
  cases result : source.result with
  | some pair => rcases pair with ⟨value, current⟩; simp [observe, result]
  | none =>
    cases selected : selectedPrimitive source.control with
    | none => simp [observe, result, selected]
    | some active =>
      cases ran : (actions.step active.site.opcode active.site.input).run source.store <;>
        simp [observe, result, selected, ran]

private theorem selected_result_none {active : ActivePrimitive m final}
    (selected : selectedPrimitive source.control = some active) : source.result = none := by
  cases source with
  | mk state store =>
    cases state with
    | eval => rfl
    | returned => cases selected

private theorem absent_iff {active : ActivePrimitive m final} :
    (actions.toPrimitives.step active.site.opcode active.site.input).run source.store = _root_.Part.none ↔
      (actions.step active.site.opcode active.site.input).run source.store = none := by
  change _root_.Part.ofOption ((actions.step active.site.opcode active.site.input).run source.store) = _root_.Part.none ↔ _
  cases (actions.step active.site.opcode active.site.input).run source.store <;> simp [_root_.Part.ofOption]

theorem observe_blocked {active : ActivePrimitive m final} {store : σ} :
    observe actions source = .blocked active store ↔
      selectedPrimitive source.control = some active ∧ source.store = store ∧
        (actions.toPrimitives.step active.site.opcode active.site.input).run source.store = _root_.Part.none := by
  rw [absent_iff]
  cases result : source.result with
  | some pair =>
    rcases pair with ⟨value, current⟩
    constructor
    · simp [observe, result]
    · rintro ⟨selected, _, _⟩
      rw [selected_result_none selected] at result
      cases result
  | none =>
    cases selected : selectedPrimitive source.control with
    | none => simp [observe, result, selected]
    | some actual =>
      cases ran : (actions.step actual.site.opcode actual.site.input).run source.store with
      | none =>
        simp only [observe, result, selected, ran, Observation.blocked.injEq, Option.some.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, ran⟩
        · rintro ⟨rfl, rfl, _⟩
          exact ⟨rfl, rfl⟩
      | some values =>
        simp only [observe, result, selected, ran, reduceCtorEq, Option.some.injEq, false_iff]
        rintro ⟨rfl, _, absent⟩
        rw [ran] at absent
        cases absent

theorem observe_suspended :
    observe actions source = .suspended source ↔ ∃ target, Step actions.toPrimitives source target := by
  cases result : source.result with
  | some value =>
    obtain ⟨values, store⟩ := value
    have done := result_iff.mp result
    rw [done]
    simp [observe, Config.result, State.result, next?, selectedPrimitive, State.next, step_iff]
  | none =>
    cases selected : selectedPrimitive source.control with
    | none =>
      simp only [observe, result, selected, true_iff]
      rcases source.progress (primitives := actions.toPrimitives) with ⟨values, done⟩ | ⟨_, blocked, _⟩ | stepped
      · have returned : source.result = some (values, source.store) := by rw [Config.result, done]; rfl
        rw [result] at returned
        cases returned
      · rw [selected] at blocked
        cases blocked
      · exact stepped
    | some active =>
      cases ran : (actions.step active.site.opcode active.site.input).run source.store <;>
        simp [observe, result, selected, ran, step_iff, next?]

theorem returns_iff_run {job : Job m final} {initial store : σ} {values : Tuple m.Val final} :
    Eval actions.toPrimitives job initial (.returned values store) ↔
      ∃ fuel, run actions fuel job initial = .returned values store := by
  rw [returns_iff_path, reachable_iff]
  simp only [run, observe_returned]

private theorem selected_eval (active : ActivePrimitive m final) :
    selectedPrimitive (.eval active.site.job active.stack) = some active := by
  cases active with
  | mk site _ => cases site; rfl

theorem blocks_iff_run {job : Job m final} {initial store : σ} {active : ActivePrimitive m final} :
    (∃ pending, Eval actions.toPrimitives job initial (.blocked active.site pending store) ∧
      active.stack = pending.push .halt) ↔
      ∃ fuel, run actions fuel job initial = .blocked active store := by
  constructor
  · rintro ⟨pending, ran, stack⟩
    let target : Config m σ final := ⟨.eval active.site.job active.stack, store⟩
    have reached : ReflTransGen (Step actions.toPrimitives) ⟨start job, initial⟩ target := by
      dsimp only [target]
      rw [stack]
      exact ran.steps .halt
    obtain ⟨fuel, same⟩ := reachable_iff.mp reached
    have blocked : target.Blocked actions.toPrimitives := by
      dsimp only [target]
      rw [stack]
      exact ran.blocks .halt
    obtain ⟨chosen, actual, absent⟩ := blocked
    have equal : active = chosen := Option.some.inj ((selected_eval active).symm.trans actual)
    subst chosen
    exact ⟨fuel, by unfold run; rw [same]; exact observe_blocked.mpr ⟨selected_eval active, rfl, absent⟩⟩
  · rintro ⟨fuel, seen⟩
    have reached := runFor_reachable actions fuel (⟨start job, initial⟩ : Config m σ final)
    obtain ⟨selected, storeEq, absent⟩ := observe_blocked.mp seen
    obtain ⟨site, pending, ran, same⟩ :=
      blocked_iff_path.mpr ⟨reached, ⟨active, selected, absent⟩⟩
    have observed : selectedPrimitive (.eval site.job (pending.push .halt)) = some active := same ▸ selected
    have equal : (⟨site, pending.push .halt⟩ : ActivePrimitive m final) = active :=
      Option.some.inj ((selected_eval ⟨site, pending.push .halt⟩).symm.trans observed)
    subst active
    exact ⟨pending, by rw [← storeEq]; exact ran, rfl⟩

theorem infinite_iff_all_suspended :
    InfiniteTrace (Step actions.toPrimitives) source ↔
      ∀ fuel, observe actions (runFor actions fuel source) = .suspended (runFor actions fuel source) := by
  constructor
  · intro live fuel
    have suffix := RightUnique.infinite_of_reach
      (R := Step actions.toPrimitives) (fun _ _ _ l r => _root_.Part.mem_unique l r)
      (runFor_reachable actions fuel source) live
    obtain ⟨target, edge, _⟩ := suffix.unfold
    exact observe_suspended.mpr ⟨target, edge⟩
  · intro all
    refine ⟨fun fuel => runFor actions fuel source, rfl, ?_⟩
    intro fuel
    obtain ⟨target, edge⟩ := observe_suspended.mp (all fuel)
    change Step actions.toPrimitives (runFor actions fuel source) (runFor actions (fuel + 1) source)
    rw [runFor_add]
    simpa only [runFor, step_iff.mp edge] using edge

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Proofs
