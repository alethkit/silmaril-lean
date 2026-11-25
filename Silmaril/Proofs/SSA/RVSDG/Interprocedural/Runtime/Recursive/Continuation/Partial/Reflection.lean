module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Machine
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Evaluation

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Proofs

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {source target endpoint : Config m σ final}

/-- A completed subjob passes its tuple and store to the residual stack.
A blocked subjob instead determines the entire endpoint, including that stack. -/
private def after (endpoint : Config m σ final) (stack : Stack m ports final)
    (rest : Tuple m.Val ports → σ → Prop) : Outcome m σ ports → Prop
  | .returned value store => rest value store
  | .blocked site pending store => Config.mk (.eval site.job (pending.push stack)) store = endpoint

/-- Interpret a returned tuple's residual stack using only finite evaluations.
This generalizes the total machine's residual-stack argument to blocked jobs. -/
private def accepts (primitives : Primitives m σ) (endpoint : Config m σ final) :
    {current : Ports (Ty V S)} → Stack m current final → Tuple m.Val current → σ → Prop
  | _, .halt, value, store => Config.mk (.returned value .halt) store = endpoint
  | _, .resume suffix entry locals outer, value, store =>
    ∃ outcome, Eval primitives (.region suffix entry (locals.snoc value)) store outcome ∧
      after endpoint outer (accepts primitives endpoint outer) outcome
  | _, .loop body outer, .cons tag carried, store =>
    if tag.selector.val == 1 then
      ∃ outcome, Eval primitives (.iteration body carried) store outcome ∧
        after endpoint outer (accepts primitives endpoint outer) outcome
    else
      accepts primitives endpoint outer carried store

private def observes (primitives : Primitives m σ) (endpoint : Config m σ final) :
    Config m σ final → Prop
  | ⟨.eval job stack, store⟩ =>
    ∃ outcome, Eval primitives job store outcome ∧
      after endpoint stack (accepts primitives endpoint stack) outcome
  | ⟨.returned value stack, store⟩ => accepts primitives endpoint stack value store

private theorem rewind {next : Config m σ final} (edge : Step primitives source target)
    (picked : Step primitives source next) (known : observes primitives endpoint target) :
    observes primitives endpoint next :=
  step_deterministic edge picked ▸ known

private theorem eval_before {first second : Job m ports} {frame : Stack m ports final} {store : σ}
    (wrap : ∀ outcome, Eval primitives second store outcome → Eval primitives first store outcome)
    (known : observes primitives endpoint ⟨.eval second frame, store⟩) :
    observes primitives endpoint ⟨.eval first frame, store⟩ := by
  obtain ⟨outcome, ran, rest⟩ := known
  exact ⟨outcome, wrap outcome ran, rest⟩

private theorem before_iteration {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
    (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (input : Tuple m.Val carried) (stack : Stack m carried final) (store : σ)
    (known : observes primitives endpoint ⟨.eval (.region body input PUnit.unit) (.loop body stack), store⟩) :
    observes primitives endpoint ⟨.eval (.iteration body input) stack, store⟩ := by
  obtain ⟨outcome, activation, rest⟩ := known
  cases outcome with
  | blocked site pending stopped =>
    exact ⟨_, .loopBlocked activation, rest⟩
  | returned value middle =>
    cases value with
    | cons tag values =>
      change accepts primitives endpoint (.loop body stack) (.cons tag values) middle at rest
      by_cases feedback : (tag.selector.val == 1) = true
      · rw [accepts, ite_eq_left feedback] at rest
        obtain ⟨outcome, later, observed⟩ := rest
        exact ⟨outcome, .again activation feedback later, observed⟩
      · rw [accepts, ite_eq_right feedback] at rest
        have done : (tag.selector.val == 1) = false := Bool.eq_false_iff.mpr feedback
        exact ⟨_, .stop activation done, rest⟩

private theorem before_step (edge : Step primitives source target)
    (known : observes primitives endpoint target) : observes primitives endpoint source := by
  rcases source with ⟨control, store⟩
  cases control with
  | returned value stack =>
    cases stack with
    | halt =>
      exact False.elim (_root_.Part.notMem_none target edge)
    | resume suffix entry locals outer =>
      change observes primitives endpoint ⟨.eval (.region suffix entry (locals.snoc value)) outer, store⟩
      exact rewind edge (pure_step rfl) known
    | loop body outer =>
      cases value with
      | cons tag values =>
        have next := rewind edge
          (pure_step (target := ⟨State.finishLoop body tag values outer, store⟩) rfl) known
        change accepts primitives endpoint (.loop body outer) (.cons tag values) store
        unfold State.finishLoop at next
        split at next <;> rename_i condition
        · rwa [accepts, ite_eq_left condition]
        · rwa [accepts, ite_eq_right condition]
  | eval job stack =>
    cases job with
    | call callee arguments =>
      exact eval_before (fun _ ran => .call ran) <| rewind edge
        (pure_step (target := ⟨.eval (Job.openClosure m callee arguments) stack, store⟩) rfl) known
    | iteration body input =>
      exact before_iteration body input stack store <| rewind edge
        (pure_step (target := ⟨.eval (.region body input PUnit.unit) (.loop body stack), store⟩) rfl) known
    | region term entry locals =>
      cases term with
      | ret wires =>
        exact ⟨_, .ret wires entry locals store, rewind edge
          (pure_step (target := ⟨.returned (wires.read entry locals) stack, store⟩) rfl) known⟩
      | bind node children suffix =>
        let frame := Stack.resume suffix entry locals stack
        let job := Job.node node.kind node.childSigs children (node.inputs.read entry locals)
        obtain ⟨outcome, first, rest⟩ := rewind edge
          (pure_step (target := ⟨.eval job frame, store⟩) rfl) known
        cases outcome with
        | blocked site pending stopped =>
          exact ⟨_, .bindBlocked first, rest⟩
        | returned value middle =>
          obtain ⟨outcome, more, observed⟩ := rest
          exact ⟨outcome, .bind first more, observed⟩
    | node kind cs children input =>
      cases kind with
      | theta =>
        exact eval_before (fun _ ran => .theta ran) <| rewind edge
          (pure_step (target := ⟨.eval (.iteration (children (0 : Fin 1)) input) stack, store⟩) rfl) known
      | base shape =>
        cases shape with
        | gamma extra =>
          cases input with
          | cons choice entry =>
            cases choice with
            | control tag =>
              exact eval_before (fun _ ran => .gamma ran) <| rewind edge
                (pure_step (target := ⟨.eval (.region (children tag) entry PUnit.unit) stack, store⟩) rfl) known
        | simple instruction =>
          cases instruction with
          | apply fn =>
            cases input with
            | cons callee arguments =>
              exact eval_before (fun _ ran => .apply ran) <| rewind edge
                (pure_step (target := ⟨.eval (.call callee arguments) stack, store⟩) rfl) known
          | primitive opcode =>
            let site : Site m := ⟨_, _, opcode, cs, children, input⟩
            change target ∈ ((primitives.step opcode input).run store).map
              (fun (value, newStore) => Config.mk (.returned value stack) newStore) at edge
            obtain ⟨⟨value, finalStore⟩, defined, rfl⟩ := (_root_.Part.mem_map_iff _).mp edge
            exact ⟨_, .primitive site defined, known⟩

private theorem before_path (path : ReflTransGen (Step primitives) source target)
    (known : observes primitives endpoint target) : observes primitives endpoint source := by
  induction path with
  | refl => exact known
  | tail _ edge ih => exact ih (before_step edge known)

private theorem observes_blocked (blocked : target.Blocked primitives) : observes primitives target target := by
  obtain ⟨active, selected, undefined⟩ := blocked
  rcases target with ⟨control, store⟩
  cases control with
  | returned => cases selected
  | eval job stack =>
    cases job with
    | call => cases selected
    | region => cases selected
    | iteration => cases selected
    | node kind cs children input =>
      cases kind with
      | theta => cases selected
      | base shape =>
        cases shape with
        | gamma => cases selected
        | simple instruction =>
          cases instruction with
          | apply => cases selected
          | primitive opcode =>
            cases selected
            exact ⟨_, .primitiveBlocked ⟨_, _, opcode, cs, children, input⟩ store undefined, rfl⟩

theorem reflect_return {job : Job m final} {store finalStore : σ} {value : Tuple m.Val final}
    (path : ReflTransGen (Step primitives) ⟨start job, store⟩ ⟨.returned value .halt, finalStore⟩) :
    Eval primitives job store (.returned value finalStore) := by
  obtain ⟨outcome, evaluated, observed⟩ := before_path path
    (show observes primitives ⟨.returned value .halt, finalStore⟩ ⟨.returned value .halt, finalStore⟩ from rfl)
  cases outcome with
  | returned output stopped =>
    change Config.mk (.returned output .halt) stopped = Config.mk (.returned value .halt) finalStore at observed
    cases observed
    exact evaluated
  | blocked site pending stopped => cases observed

theorem reflect_blocked {job : Job m final} {store : σ}
    (path : ReflTransGen (Step primitives) ⟨start job, store⟩ target)
    (blocked : target.Blocked primitives) :
    ∃ site pending, Eval primitives job store (.blocked site pending target.store) ∧
      target.control = .eval site.job (pending.push .halt) := by
  obtain ⟨outcome, evaluated, observed⟩ := before_path path (observes_blocked blocked)
  cases outcome with
  | returned value stopped =>
    change Config.mk (.returned value .halt) stopped = target at observed
    subst target
    obtain ⟨_, selected, _⟩ := blocked
    cases selected
  | blocked site pending stopped =>
    change Config.mk (.eval site.job (pending.push .halt)) stopped = target at observed
    subst target
    exact ⟨site, pending, evaluated, rfl⟩

theorem blocked_iff_path {job : Job m final} {store : σ} :
    (∃ site pending, Eval primitives job store (.blocked site pending target.store) ∧
      target.control = .eval site.job (pending.push .halt)) ↔
      ReflTransGen (Step primitives) ⟨start job, store⟩ target ∧ target.Blocked primitives := by
  constructor
  · rcases target with ⟨control, stopped⟩
    rintro ⟨site, pending, evaluated, rfl⟩
    exact ⟨eval_steps evaluated .halt, eval_blocked evaluated .halt⟩
  · rintro ⟨path, blocked⟩
    exact reflect_blocked path blocked

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Proofs
