module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Proofs

open Descent (stackDepth)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ}

/-- Replace the local halt by the actual enclosing frame. -/
private def attach (frame : Stack m ports final) :
    {current : Ports (Ty V S)} → Stack m current ports → Stack m current final
  | _, .halt => frame
  | _, .resume suffix entry locals rest => .resume suffix entry locals (attach frame rest)
  | _, .loop body rest => .loop body (attach frame rest)

private def underState (frame : Stack m ports final) : State m ports → State m final
  | .eval job stack => .eval job (attach frame stack)
  | .returned value stack => .returned value (attach frame stack)

private def under (frame : Stack m ports final) (source : Config m σ ports) : Config m σ final :=
  ⟨underState frame source.control, source.store⟩

private theorem depth_attach (frame : Stack m ports final) {current : Ports (Ty V S)}
    (stack : Stack m current ports) : stackDepth (attach frame stack) = stackDepth frame + stackDepth stack := by
  induction stack with
  | halt => exact (Nat.add_zero _).symm
  | resume _ _ _ _ ih => exact congrArg (· + 1) (ih frame)
  | loop _ _ ih => exact congrArg (· + 1) (ih frame)

private def stateDepth : State m final → Nat
  | .eval _ stack | .returned _ stack => stackDepth stack

private theorem return_under {frame : Stack m ports final} {state : State m ports}
    {value : Tuple m.Val ports} (returned : underState frame state = .returned value frame) :
    state = .returned value .halt := by
  cases state with
  | eval => cases returned
  | returned actual stack =>
    have same : stackDepth (attach frame stack) = stackDepth frame := congrArg stateDepth returned
    have empty : stackDepth stack = 0 := by rw [depth_attach] at same; omega
    cases stack with
    | halt => cases returned; rfl
    | resume => cases empty
    | loop => cases empty

private theorem next_under (frame : Stack m ports final) (source : Config m σ ports)
    (live : ¬ Continuation.Feedback.atReturn (.halt : Stack m ports ports) source.control) :
    (under frame source).next primitives = (source.next primitives).map (under frame) := by
  rcases source with ⟨control, store⟩
  cases control with
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
          | apply => cases input; rfl
          | primitive opcode =>
            let action := (primitives.step opcode input).run store
            change action.map (fun (output, store') => Config.mk (.returned output (attach frame stack)) store') =
              (action.map (fun (output, store') => Config.mk (.returned output stack) store')).map (under frame)
            rw [_root_.Part.map_map]
            rfl
  | returned value stack =>
    cases stack with
    | halt => exact False.elim (live ⟨value, rfl⟩)
    | resume => rfl
    | loop body rest =>
      cases value with
      | cons tag carried =>
        change _root_.Part.some (Config.mk (State.finishLoop body tag carried (attach frame rest)) store) =
          (_root_.Part.some (Config.mk (State.finishLoop body tag carried rest) store)).map (under frame)
        unfold State.finishLoop
        split <;> rfl

private theorem step_from_under {frame : Stack m ports final} {source : Config m σ ports}
    {target : Config m σ final} (edge : InsideStep primitives frame (under frame source) target) :
    ∃ next, Step primitives source next ∧ under frame next = target := by
  have live : ¬ Continuation.Feedback.atReturn (.halt : Stack m ports ports) source.control := by
    rintro ⟨value, returned⟩
    exact edge.2 ⟨value, congrArg (underState frame) returned⟩
  have actual := edge.1
  change target ∈ (under frame source).next primitives at actual
  rw [next_under frame source live] at actual
  exact (_root_.Part.mem_map_iff _).mp actual

private theorem path_from_under (frame : Stack m ports final) {source : Config m σ ports}
    {target : Config m σ final} (path : ReflTransGen (InsideStep primitives frame) (under frame source) target) :
    ∃ next, ReflTransGen (Step primitives) source next ∧ under frame next = target := by
  induction path with
  | refl => exact ⟨source, .refl, rfl⟩
  | tail _ edge ih =>
    obtain ⟨middle, path, rfl⟩ := ih
    obtain ⟨next, step, exactTarget⟩ := step_from_under edge
    exact ⟨next, path.tail step, exactTarget⟩

theorem returns_of_delimited (frame : Stack m ports final) {job : Job m ports} {store finalStore : σ}
    {value : Tuple m.Val ports}
    (path : ReflTransGen (InsideStep primitives frame) ⟨.eval job frame, store⟩
      ⟨.returned value frame, finalStore⟩) : Eval primitives job store (.returned value finalStore) := by
  obtain ⟨next, localPath, finished⟩ := path_from_under frame (source := ⟨start job, store⟩) path
  have control : next.control = .returned value .halt := return_under (congrArg Config.control finished)
  have state : next.store = finalStore := congrArg Config.store finished
  have same : next = ⟨.returned value .halt, finalStore⟩ := by cases next; cases control; cases state; rfl
  exact returns_iff_path.mpr (same ▸ localPath)

private theorem under_at {micro : Nat → Config m σ final} {begin : Nat}
    (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    (frame : Stack m ports final) {job : Job m ports}
    (opened : (micro begin).control = .eval job frame) (count : Nat)
    (within : ∀ offset, offset < count →
      ¬ Continuation.Feedback.atReturn frame (micro (begin + offset)).control) :
    ∃ localState : Config m σ ports, under frame localState = micro (begin + count) := by
  induction count with
  | zero =>
    refine ⟨⟨start job, (micro begin).store⟩, ?_⟩
    rw [Nat.add_zero]
    change Config.mk (.eval job frame) (micro begin).store = micro begin
    rw [← opened]
  | succ count ih =>
    obtain ⟨localState, observed⟩ := ih (fun offset before => within offset (by omega))
    have edge : InsideStep primitives frame (under frame localState) (micro (begin + count + 1)) :=
      ⟨observed.symm ▸ steps (begin + count), observed.symm ▸ within count (Nat.lt_succ_self _)⟩
    obtain ⟨next, _, exactTarget⟩ := step_from_under edge
    exact ⟨next, exactTarget⟩

private theorem depth_under (frame : Stack m ports final) (localState : State m ports) :
    stateDepth (underState frame localState) = stackDepth frame + stateDepth localState := by
  cases localState with
  | eval _ stack | returned _ stack => exact depth_attach frame stack

private theorem return_at_floor {frame : Stack m ports final} {localState : State m ports}
    {other : Ports (Ty V S)} {otherFrame : Stack m other final} {value : Tuple m.Val other}
    (observed : underState frame localState = .returned value otherFrame)
    (low : stackDepth otherFrame ≤ stackDepth frame) :
    Continuation.Feedback.atReturn frame (.returned value otherFrame) := by
  have depths : stackDepth otherFrame = stackDepth frame + stateDepth localState :=
    (congrArg stateDepth observed).symm.trans (depth_under frame localState)
  have empty : stateDepth localState = 0 := by omega
  cases localState with
  | eval => cases observed
  | returned values stack =>
    cases stack with
    | halt => exact ⟨values, observed.symm⟩
    | resume => cases empty
    | loop => cases empty

theorem return_before_live {other : Ports (Ty V S)} {micro : Nat → Config m σ final}
    {begin finish : Nat} {job : Job m ports} {next : Job m other}
    {frame : Stack m ports final} {child : Stack m other final}
    (steps : ∀ i, Step primitives (micro i) (micro (i + 1))) (ordered : begin < finish)
    (entered : (micro begin).control = .eval job frame) (selected : (micro finish).control = .eval next child)
    (lives : ∀ i, finish ≤ i → ¬ Continuation.Feedback.atReturn child (micro i).control)
    (returns : ∃ i, begin < i ∧ Continuation.Feedback.atReturn frame (micro i).control) :
    ∃ i, begin < i ∧ i < finish ∧ Continuation.Feedback.atReturn frame (micro i).control := by
  classical
  by_contra noEarlierReturn
  have stillOpen (offset : Nat) (before : offset < finish - begin) :
      ¬ Continuation.Feedback.atReturn frame (micro (begin + offset)).control := by
    intro returned
    cases offset with
    | zero =>
      obtain ⟨_, done⟩ := returned
      rw [Nat.add_zero, entered] at done
      cases done
    | succ offset => exact noEarlierReturn ⟨_, by omega, by omega, returned⟩
  obtain ⟨current, reached⟩ := under_at steps frame entered (finish - begin) stillOpen
  rw [Nat.add_sub_of_le (Nat.le_of_lt ordered)] at reached
  have enteredChild := (congrArg Config.control reached).trans selected
  have depthChild : stackDepth child = stackDepth frame + stateDepth current.control :=
    (congrArg stateDepth enteredChild).symm.trans (depth_under frame current.control)
  obtain ⟨stop, afterBegin, value, returned⟩ := returns
  have afterFinish : finish ≤ stop := by
    by_contra tooSoon
    exact noEarlierReturn ⟨stop, afterBegin, by omega, value, returned⟩
  obtain ⟨atStop, inside⟩ := under_at steps child selected (stop - finish)
    (fun i _ => lives (finish + i) (Nat.le_add_right _ _))
  rw [Nat.add_sub_of_le afterFinish] at inside
  have atEarlierFrame := (congrArg Config.control inside).trans returned
  exact lives stop afterFinish (returned ▸ return_at_floor atEarlierFrame (by omega))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Proofs
