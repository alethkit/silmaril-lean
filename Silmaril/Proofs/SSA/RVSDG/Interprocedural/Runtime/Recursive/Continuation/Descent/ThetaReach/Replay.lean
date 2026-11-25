module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Proofs

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {job : Job m ports} {target : Restart m} {pending : Pending m target.carried ports}

theorem reaches_steps (reached : Reaches m job target pending) (stack : Stack m ports final) :
    ReflTransGen Step (.eval job stack) (target.state (pending.push stack)) := by
  induction reached with
  | restart completed => exact Feedback.iterations_steps completed stack
  | @later args head ports past tail node children rest entry locals value target pending returned reached ih =>
    let frame := Stack.resume rest entry locals stack
    have completed := (Feedback.returns_iff_delimited frame).mp returned
    have ordinary := ReflTransGen.mono (fun _ _ (edge : Feedback.InsideStep frame _ _) => edge.1) _ _ completed
    have entered : Step (.eval (.region (.bind node children rest) entry locals) stack)
        (.eval (.node node.kind node.childSigs children (node.inputs.read entry locals)) frame) := rfl
    have resumed : Step (.returned value frame) (.eval (.region rest entry (locals.snoc value)) stack) := rfl
    exact ((ordinary.head entered).tail resumed).trans (ih stack)
  | @inside args head ports past tail node children rest entry locals target pending reached ih =>
    exact (ih (.resume rest entry locals stack)).head rfl
  | gamma _ ih => exact (ih stack).head rfl
  | theta _ ih => exact (ih stack).head rfl
  | @iteration carried sigs body input current target pending completed active ih =>
    have entered : Step (Feedback.restart body stack current)
        (.eval (.region body current PUnit.unit) (.loop body stack)) := rfl
    exact ((Feedback.iterations_steps completed stack).tail entered).trans (ih (.loop body stack))

private theorem feedback_infinite (target : Restart m) (stack : Stack m target.carried final)
    (productive : Feedback.Run target.body target.input) : InfiniteTrace Step (target.state stack) := by
  obtain ⟨inputs, micro, indices, first, trace⟩ := (Feedback.run_iff_restarts (parent := stack)).mp productive
  have initial := trace.atRestart 0
  rw [trace.first, first] at initial
  exact ⟨micro, initial, trace.steps⟩

theorem route_infinite {caller : Entry m} {stack : Stack m caller.results final}
    (route : FeedbackRoute m caller stack) : InfiniteTrace Step (caller.state stack) := by
  induction route with
  | @restart caller stack target pending reaches productive =>
    have entered : Step (caller.state stack) (.eval caller.openBody stack) := rfl
    exact InfiniteTrace.of_steps ((reaches_steps reaches stack).head entered)
      (feedback_infinite target (pending.push stack) productive)
  | call reaches _ ih =>
    exact InfiniteTrace.of_steps (entry_microsteps reaches _).to_reflTransGen ih

theorem diverges_sound {entry : Entry m} (certificate : Diverges entry) :
    InfiniteTrace Step (entry.state .halt) := by
  rcases certificate with ⟨run, first⟩ | route
  · subst entry
    exact run.infinite .halt
  · exact route_infinite route

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Proofs
