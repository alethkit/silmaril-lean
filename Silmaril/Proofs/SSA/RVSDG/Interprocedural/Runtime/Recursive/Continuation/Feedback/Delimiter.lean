module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Proofs

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {current final : Ports (Ty V S)}

/-- Replace the local halt by an enclosing stack. -/
private def attach (frame : Stack m current final) :
    {ports : Ports (Ty V S)} → Stack m ports current → Stack m ports final
  | _, .halt => frame
  | _, .resume suffix entry locals rest => .resume suffix entry locals (attach frame rest)
  | _, .loop body rest => .loop body (attach frame rest)

private def under (frame : Stack m current final) : State m current → State m final
  | .eval job stack => .eval job (attach frame stack)
  | .returned value stack => .returned value (attach frame stack)

private def height : {ports final : Ports (Ty V S)} → Stack m ports final → Nat
  | _, _, .halt => 0
  | _, _, .resume _ _ _ rest => height rest + 1
  | _, _, .loop _ rest => height rest + 1

private theorem height_attach (frame : Stack m current final) {ports : Ports (Ty V S)}
    (stack : Stack m ports current) : height (attach frame stack) = height frame + height stack := by
  induction stack with
  | halt => exact (Nat.add_zero _).symm
  | resume _ _ _ _ ih => exact congrArg (· + 1) (ih frame)
  | loop _ _ ih => exact congrArg (· + 1) (ih frame)

private def stateHeight : State m final → Nat
  | .eval _ stack | .returned _ stack => height stack

private theorem return_under {frame : Stack m current final} {state : State m current}
    {output : Tuple m.Val current} (same : under frame state = .returned output frame) :
    state = .returned output .halt := by
  cases state with
  | eval => cases same
  | returned value stack =>
    have len : height (attach frame stack) = height frame := congrArg stateHeight same
    have empty : height stack = 0 := by rw [height_attach] at len; omega
    cases stack with
    | halt => cases same; rfl
    | resume => cases empty
    | loop => cases empty

private theorem next_under (frame : Stack m current final) (state : State m current)
    (notDone : ∀ value : Tuple m.Val current, state ≠ .returned value .halt) :
    (under frame state).next = state.next.map (under frame) := by
  cases state with
  | eval job stack =>
    cases job with
    | call => rfl
    | region body => cases body <;> rfl
    | iteration => rfl
    | node kind cs children input =>
      cases kind with
      | theta => rfl
      | base shape =>
        cases shape with
        | gamma => cases input; rfl
        | simple instruction =>
          cases instruction with
          | primitive => rfl
          | apply => cases input; rfl
  | returned value stack =>
    cases stack with
    | halt => exact False.elim (notDone value rfl)
    | resume => rfl
    | loop body rest =>
      cases value with
      | cons tag carried =>
        change some (State.finishLoop body tag carried (attach frame rest)) =
          (some (State.finishLoop body tag carried rest)).map (under frame)
        by_cases continues : (tag.selector.val == 1) = true
        · simp only [State.finishLoop, ite_eq_left continues]; rfl
        · simp only [State.finishLoop, ite_eq_right continues]; rfl

private theorem step_under (frame : Stack m current final) {source target : State m current}
    (edge : Step source target) : InsideStep frame (under frame source) (under frame target) := by
  have notDone (value : Tuple m.Val current) (done : source = .returned value .halt) : False := by
    subst source
    cases edge
  refine ⟨?_, fun ⟨value, done⟩ => notDone value (return_under done)⟩
  change (under frame source).next = some (under frame target)
  rw [next_under frame source notDone, show source.next = some target from edge]
  rfl

private theorem step_from_under {frame : Stack m current final} {source : State m current}
    {target : State m final} (edge : InsideStep frame (under frame source) target) :
    ∃ next, Step source next ∧ under frame next = target := by
  have notDone (value : Tuple m.Val current) (done : source = .returned value .halt) :
      False := edge.2 ⟨value, by rw [done]; rfl⟩
  have actual : (under frame source).next = some target := edge.1
  rw [next_under frame source notDone] at actual
  cases picked : source.next with
  | none => rw [picked] at actual; cases actual
  | some next =>
    rw [picked] at actual
    exact ⟨next, picked, Option.some.inj actual⟩

private theorem path_from_under (frame : Stack m current final) {source : State m current}
    {target : State m final} (trace : ReflTransGen (InsideStep frame) (under frame source) target) :
    ∃ next, ReflTransGen Step source next ∧ under frame next = target := by
  induction trace with
  | refl => exact ⟨source, .refl, rfl⟩
  | tail _ edge ih =>
    obtain ⟨middle, path, rfl⟩ := ih
    obtain ⟨next, step, same⟩ := step_from_under edge
    exact ⟨next, path.tail step, same⟩

theorem returns_iff_delimited (frame : Stack m current final) {job : Job m current}
    {value : Tuple m.Val current} :
    Returns m job value ↔ ReflTransGen (InsideStep frame) (.eval job frame) (.returned value frame) := by
  constructor
  · intro returns
    exact ReflTransGen.lift (under frame) (fun _ _ => step_under frame) _ _ (completes_of_returns returns)
  · intro path
    obtain ⟨next, localPath, finished⟩ := path_from_under frame (source := start job) path
    rw [return_under finished] at localPath
    exact completes_sound localPath

private theorem state_step (state : State m current)
    (notDone : ∀ value : Tuple m.Val current, state ≠ .returned value .halt) :
    ∃ next, Step state next := by
  cases picked : state.next with
  | some next => exact ⟨next, picked⟩
  | none =>
    cases result : state.result with
    | none => exact False.elim (no_unsupported state ⟨picked, result⟩)
    | some value =>
      cases state with
      | eval => cases result
      | returned actual stack =>
        cases stack with
        | halt => exact False.elim (notDone actual rfl)
        | resume => cases result
        | loop => cases result

theorem trace_without_return (frame : Stack m current final) (job : Job m current)
    (noReturn : ∀ value, ¬ Returns m job value) :
    InfiniteTrace (InsideStep frame) (.eval job frame) := by
  apply InfiniteTrace.coinduct
    (fun state => ∃ localState, ReflTransGen Step (start job) localState ∧ under frame localState = state)
    ?_ ⟨start job, .refl, rfl⟩
  rintro state ⟨localState, ran, rfl⟩
  have notDone (value : Tuple m.Val current) (finished : localState = .returned value .halt) : False :=
    by
      rw [finished] at ran
      exact noReturn value (completes_sound ran)
  obtain ⟨next, edge⟩ := state_step localState notDone
  exact ⟨under frame next, step_under frame edge, next, ran.tail edge, rfl⟩

private theorem under_at {micro : Nat → State m final} {begin : Nat}
    (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (frame : Stack m current final) {job : Job m current}
    (opened : micro begin = .eval job frame) (count : Nat)
    (within : ∀ offset, offset < count → ¬ atReturn frame (micro (begin + offset))) :
    ∃ localState : State m current, under frame localState = micro (begin + count) := by
  induction count with
  | zero => exact ⟨start job, opened.symm⟩
  | succ count ih =>
    obtain ⟨localState, observed⟩ := ih (fun offset before => within offset (by omega))
    have edge : InsideStep frame (under frame localState) (micro (begin + count + 1)) :=
      ⟨observed.symm ▸ steps (begin + count), observed.symm ▸ within count (Nat.lt_succ_self _)⟩
    obtain ⟨next, _, observed⟩ := step_from_under edge
    exact ⟨next, observed⟩

private theorem height_under (frame : Stack m current final) (localState : State m current) :
    stateHeight (under frame localState) = height frame + stateHeight localState := by
  cases localState with
  | eval _ stack | returned _ stack => exact height_attach frame stack

private theorem return_at_floor {frame : Stack m current final} {localState : State m current}
    {other : Ports (Ty V S)} {otherFrame : Stack m other final} {value : Tuple m.Val other}
    (observed : under frame localState = .returned value otherFrame) (low : height otherFrame ≤ height frame) :
    atReturn frame (.returned value otherFrame) := by
  have depths : height otherFrame = height frame + stateHeight localState :=
    (congrArg stateHeight observed).symm.trans (height_under frame localState)
  have empty : stateHeight localState = 0 := by omega
  cases localState with
  | eval => cases observed
  | returned value stack =>
    cases stack with
    | halt => exact ⟨value, observed.symm⟩
    | resume => cases empty
    | loop => cases empty

theorem return_before_live {other : Ports (Ty V S)} {micro : Nat → State m final}
    {begin finish : Nat} {job : Job m current} {next : Job m other}
    {frame : Stack m current final} {child : Stack m other final}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (ordered : begin < finish)
    (entered : micro begin = .eval job frame) (selected : micro finish = .eval next child)
    (lives : ∀ i, finish ≤ i → ¬ atReturn child (micro i))
    (returns : ∃ i, begin < i ∧ atReturn frame (micro i)) :
    ∃ i, begin < i ∧ i < finish ∧ atReturn frame (micro i) := by
  classical
  by_contra noEarlierReturn
  have stillOpen (offset : Nat) (before : offset < finish - begin) :
      ¬ atReturn frame (micro (begin + offset)) := by
    intro returned
    cases offset with
    | zero =>
      obtain ⟨_, done⟩ := returned
      rw [Nat.add_zero, entered] at done
      cases done
    | succ offset => exact noEarlierReturn ⟨_, by omega, by omega, returned⟩
  obtain ⟨current, reached⟩ := under_at steps frame entered (finish - begin) stillOpen
  rw [Nat.add_sub_of_le (Nat.le_of_lt ordered), selected] at reached
  have depthChild : height child = height frame + stateHeight current :=
    (congrArg stateHeight reached).symm.trans (height_under frame current)
  obtain ⟨stop, afterBegin, value, returned⟩ := returns
  have afterFinish : finish ≤ stop := by
    by_contra tooSoon
    exact noEarlierReturn ⟨stop, afterBegin, by omega, value, returned⟩
  obtain ⟨atStop, inside⟩ := under_at steps child selected (stop - finish)
    (fun i _ => lives (finish + i) (Nat.le_add_right _ _))
  rw [Nat.add_sub_of_le afterFinish, returned] at inside
  exact lives stop afterFinish (returned ▸ return_at_floor inside (by omega))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Proofs
