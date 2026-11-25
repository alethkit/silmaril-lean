module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Proofs

open Descent (Pending)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {primitives : Primitives m σ} {carried ports final : Ports (Ty V S)}
variable {sigs : List (Ports (Ty V S))}
variable {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
variable {input next : Tuple m.Val carried × σ}

theorem iteration_steps (ran : Iteration primitives body input next) (parent : Stack m carried final) :
    TransGen (Step primitives)
      (Restart.config ⟨carried, sigs, body, input⟩ parent)
      (Restart.config ⟨carried, sigs, body, next⟩ parent) := by
  obtain ⟨tag, returned, feedback⟩ := ran
  have entered : Step primitives (Restart.config ⟨carried, sigs, body, input⟩ parent)
      ⟨.eval (.region body input.1 PUnit.unit) (.loop body parent), input.2⟩ := .of_next_some rfl
  have restarted : Step primitives ⟨.returned (.cons tag next.1) (.loop body parent), next.2⟩
      (Restart.config ⟨carried, sigs, body, next⟩ parent) := by
    apply Step.of_next_some
    change _root_.Part.some (Config.mk (State.finishLoop body tag next.1 parent) next.2) = _
    rw [State.finishLoop, ite_eq_left feedback]
    rfl
  exact (TransGen.tail' (returned.steps (.loop body parent)) restarted).head entered

private theorem iterations_steps (ran : ReflTransGen (Iteration primitives body) input next)
    (parent : Stack m carried final) :
    ReflTransGen (Step primitives)
      (Restart.config ⟨carried, sigs, body, input⟩ parent)
      (Restart.config ⟨carried, sigs, body, next⟩ parent) := by
  induction ran with
  | refl => exact .refl
  | tail _ iteration ih => exact ih.trans (iteration_steps iteration parent).to_reflTransGen

theorem run_infinite (ran : Run primitives body input) (parent : Stack m carried final) :
    InfiniteTrace (Step primitives) (Restart.config ⟨carried, sigs, body, input⟩ parent) := by
  obtain ⟨inputs, first, iterations⟩ := ran
  let boundary (i : Nat) := Restart.config ⟨carried, sigs, body, inputs i⟩ parent
  have segment (i : Nat) : TransGen (Step primitives) (boundary i) (boundary (i + 1)) :=
    iteration_steps (iterations i) parent
  rw [← first]
  apply InfiniteTrace.coinduct (fun state => ∃ n, TransGen (Step primitives) state (boundary n)) ?_
    ⟨1, segment 0⟩
  rintro state ⟨n, path⟩
  obtain ⟨next, edge, rest⟩ := TransGen.head'_iff.mp path
  refine ⟨next, edge, ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp rest with same | remaining
  · subst next
    exact ⟨n + 1, segment n⟩
  · exact ⟨n, remaining⟩

theorem reaches_steps {job : Job m ports} {store : σ} {target : Restart m σ}
    {pending : Pending m target.carried ports}
    (reached : Reaches primitives job store target pending) (frame : Stack m ports final) :
    ReflTransGen (Step primitives) ⟨.eval job frame, store⟩ (target.config (pending.push frame)) := by
  induction reached with
  | restart completed => exact iterations_steps completed frame
  | @later args head ports past tail node children rest entry locals value store middle target pending returned reached ih =>
    let saved := Stack.resume rest entry locals frame
    have entered : Step primitives ⟨.eval (.region (.bind node children rest) entry locals) frame, store⟩
        ⟨.eval (.node node.kind node.childSigs children (node.inputs.read entry locals)) saved, store⟩ :=
      .of_next_some rfl
    have resumed : Step primitives ⟨.returned value saved, middle⟩
        ⟨.eval (.region rest entry (locals.snoc value)) frame, middle⟩ := .of_next_some rfl
    exact (((returned.steps saved).head entered).tail resumed).trans (ih frame)
  | @inside args head ports past tail node children rest entry locals store target pending reached ih =>
    exact (ih (.resume rest entry locals frame)).head (.of_next_some rfl)
  | call _ ih => exact (ih frame).head (.of_next_some rfl)
  | apply _ ih => exact (ih frame).head (.of_next_some rfl)
  | gamma _ ih => exact (ih frame).head (.of_next_some rfl)
  | theta _ ih => exact (ih frame).head (.of_next_some rfl)
  | @iteration carried sigs body input current target pending completed active ih =>
    have entered : Step primitives (Restart.config ⟨carried, sigs, body, current⟩ frame)
        ⟨.eval (.region body current.1 PUnit.unit) (.loop body frame), current.2⟩ := .of_next_some rfl
    exact ((iterations_steps completed frame).tail entered).trans (ih (.loop body frame))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Proofs
