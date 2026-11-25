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

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Proofs
