module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {outs final : Ports (Ty V S)}

private abbrev Path {final : Ports (Ty V S)} :=
  Relation.ReflTransGen (Step (m := m) (outs := final))

/-- Interpret only the residual work in a stack using the independent judgment. -/
private def accepts : {current : Ports (Ty V S)} → Stack m current final →
    Tuple m.Val current → Tuple m.Val final → Prop
  | _, .halt, value, output => value = output
  | _, .resume suffix entry locals outer, value, output =>
    ∃ next, Returns m (.region suffix entry (locals.snoc value)) next ∧ accepts outer next output
  | _, .loop body outer, value, output =>
    match value with
    | .cons tag carried =>
      if tag.selector.val == 1 then
        ∃ next, Returns m (.iteration body carried) next ∧ accepts outer next output
      else accepts outer carried output

private def observes (output : Tuple m.Val final) : State m final → Prop
  | .eval job stack => ∃ value, Returns m job value ∧ accepts stack value output
  | .returned value stack => accepts stack value output

private theorem iteration_observes
    {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
    (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (input : Tuple m.Val carried) (stack : Stack m carried final) (output : Tuple m.Val final) :
    observes output (.eval (.iteration body input) stack) ↔
      observes output (.eval (.region body input PUnit.unit) (.loop body stack)) := by
  constructor
  · rintro ⟨value, returned, rest⟩
    cases returned with
    | stop activation done =>
      refine ⟨_, activation, ?_⟩
      simpa only [accepts, done, Bool.false_eq_true, ↓reduceIte] using rest
    | again activation continues later =>
      refine ⟨_, activation, ?_⟩
      simpa only [accepts, continues, ↓reduceIte] using
        (show ∃ next, Returns m (.iteration body _) next ∧ accepts stack next output from ⟨_, later, rest⟩)
  · rintro ⟨value, activation, rest⟩
    cases value with
    | cons tag carried =>
      by_cases continues : (tag.selector.val == 1) = true
      · rw [accepts, ite_eq_left continues] at rest
        obtain ⟨next, later, done⟩ := rest
        exact ⟨next, .again activation continues later, done⟩
      · rw [accepts, ite_eq_right continues] at rest
        have done : (tag.selector.val == 1) = false := by
          cases eq : (tag.selector.val == 1) <;> simp_all
        exact ⟨carried, .stop activation done, rest⟩

private def instructionReturns {ins : Ports (Ty V S)} (output : Tuple m.Val outs)
    (instruction : Instruction Op ins outs) : Tuple m.Val ins → Prop :=
  match instruction with
  | .primitive _ => fun _ => True
  | .apply _ => fun
    | .cons callee arguments => Returns m (.call callee arguments) output

private def nodeInvocations {ins : Ports (Ty V S)} (output : Tuple m.Val outs) :
    (kind : NestedTheta.Kind (Instruction Op) ins outs) →
    (cs : Fin kind.arity → List (Ports (Ty V S))) → Bodies kind cs → Tuple m.Val ins → Prop
  | .base shape, _, _, input =>
    match shape with
    | .simple instruction => instructionReturns output instruction input
    | .gamma _ => True
  | .theta _, _, children, input => Returns m (.iteration (children (0 : Fin 1)) input) output

private def invocationReturns (output : Tuple m.Val outs) : Job m outs → Prop
  | .node kind cs children input => nodeInvocations output kind cs children input
  | _ => True

private theorem invocation_returns {job : Job m outs} {output : Tuple m.Val outs}
    (returned : Returns m job output) : invocationReturns output job := by
  cases returned with
  | apply invocation => exact invocation
  | theta loop => exact loop
  | _ => exact True.intro

private theorem observes_step {source target : State m final} (edge : Step source target)
    (output : Tuple m.Val final) : observes output source ↔ observes output target := by
  cases source with
  | returned value stack =>
    cases stack with
    | halt =>
      change none = some target at edge
      cases edge
    | resume suffix entry locals outer =>
      have same : some (.eval (.region suffix entry (locals.snoc value)) outer) = some target := edge
      cases Option.some.inj same
      rfl
    | loop body outer =>
      cases value with
      | cons tag values =>
        have same : some (State.finishLoop body tag values outer) = some target := edge
        cases Option.some.inj same
        change observes output (.returned (.cons tag values) (.loop body outer)) ↔
          observes output (State.finishLoop body tag values outer)
        unfold State.finishLoop
        split <;> rename_i condition <;> simp only [observes, accepts, condition, Bool.false_eq_true, ↓reduceIte]
  | eval job stack =>
    cases job with
    | call callee arguments =>
      have same : some (.eval (Job.openClosure m callee arguments) stack) = some target := edge
      cases Option.some.inj same
      constructor
      · rintro ⟨value, ran, rest⟩
        cases ran with | call body => exact ⟨value, body, rest⟩
      · rintro ⟨value, ran, rest⟩
        exact ⟨value, .call ran, rest⟩
    | region term entry locals =>
      cases term with
      | ret wires =>
        have same : some (.returned (wires.read entry locals) stack) = some target := edge
        cases Option.some.inj same
        constructor
        · rintro ⟨_, ran, rest⟩
          cases ran
          exact rest
        · intro rest
          exact ⟨_, .ret wires entry locals, rest⟩
      | bind node children suffix =>
        have same : some (.eval (.node node.kind node.childSigs children (node.inputs.read entry locals))
            (.resume suffix entry locals stack)) = some target := edge
        cases Option.some.inj same
        constructor
        · rintro ⟨_, ran, rest⟩
          cases ran with | bind first more => exact ⟨_, first, _, more, rest⟩
        · rintro ⟨_, first, _, more, rest⟩
          exact ⟨_, .bind first more, rest⟩
    | node kind cs children input =>
      cases kind with
      | theta =>
        have same : some (.eval (.iteration (children (0 : Fin 1)) input) stack) = some target := edge
        cases Option.some.inj same
        constructor
        · rintro ⟨_, ran, rest⟩
          exact ⟨_, invocation_returns ran, rest⟩
        · rintro ⟨_, ran, rest⟩
          exact ⟨_, .theta ran, rest⟩
      | base shape =>
        cases shape with
        | simple instruction =>
          cases instruction with
          | primitive opcode =>
            have same : some (.returned (m.primitive opcode input) stack) = some target := edge
            cases Option.some.inj same
            constructor
            · rintro ⟨_, ran, rest⟩
              cases ran
              exact rest
            · intro rest
              exact ⟨_, .primitive opcode cs children input, rest⟩
          | apply fn =>
            cases input with
            | cons callee arguments =>
              have same : some (.eval (.call callee arguments) stack) = some target := edge
              cases Option.some.inj same
              constructor
              · rintro ⟨_, ran, rest⟩
                exact ⟨_, invocation_returns ran, rest⟩
              · rintro ⟨_, ran, rest⟩
                exact ⟨_, .apply ran, rest⟩
        | gamma extra =>
          cases input with
          | cons choice entry =>
            cases choice with
            | control tag =>
              have same : some (.eval (.region (children tag) entry PUnit.unit) stack) = some target := edge
              cases Option.some.inj same
              constructor
              · rintro ⟨_, ran, rest⟩
                cases ran with | gamma branch => exact ⟨_, branch, rest⟩
              · rintro ⟨_, ran, rest⟩
                exact ⟨_, .gamma ran, rest⟩
    | iteration body input =>
      have same : some (.eval (.region body input PUnit.unit) (.loop body stack)) = some target := edge
      cases Option.some.inj same
      exact iteration_observes body input stack output

private theorem observes_trace {source target : State m final} (path : Path source target)
    (output : Tuple m.Val final) : observes output source ↔ observes output target := by
  induction path with
  | refl => rfl
  | tail _ edge ih => exact ih.trans (observes_step edge output)

theorem completes_sound {job : Job m outs} {output : Tuple m.Val outs}
    (complete : Completes (start job) output) : Returns m job output := by
  obtain ⟨_, returned, rfl⟩ := (observes_trace complete output).mpr (show output = output from rfl)
  exact returned

private theorem enter_iteration {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
    (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (input : Tuple m.Val carried) (stack : Stack m carried final) :
    Step (.eval (.iteration body input) stack) (.eval (.region body input PUnit.unit) (.loop body stack)) := rfl

private theorem evaluates {job : Job m outs} {value : Tuple m.Val outs} (derivation : Returns m job value) :
    ∀ {final : Ports (Ty V S)} (stack : Stack m outs final),
      Path (.eval job stack) (.returned value stack) := by
  induction derivation with
  | call _ ih => intro final stack; exact (ih stack).head rfl
  | ret => intro final stack; exact .single rfl
  | @bind args head outs past tail node children rest entry locals value output first more firstIH restIH =>
    intro final stack
    let resume := Stack.resume rest entry locals stack
    let nodeJob := Job.node node.kind node.childSigs children (node.inputs.read entry locals)
    have enters : Step (.eval (.region (.bind node children rest) entry locals) stack) (.eval nodeJob resume) := rfl
    have resumed : Step (.returned value resume) (.eval (.region rest entry (locals.snoc value)) stack) := rfl
    exact (((firstIH resume).head enters).tail resumed).trans (restIH stack)
  | primitive => intro final stack; exact .single rfl
  | apply _ ih => intro final stack; exact (ih stack).head rfl
  | gamma _ ih => intro final stack; exact (ih stack).head rfl
  | theta _ ih => intro final stack; exact (ih stack).head rfl
  | @stop carried sigs body input output tag activation done ih =>
    intro final stack
    have exit : Step (.returned (.cons tag output) (.loop body stack)) (.returned output stack) := by
      change some (State.finishLoop body tag output stack) = some (.returned output stack)
      simp only [State.finishLoop, done, Bool.false_eq_true, ↓reduceIte]
    exact ((ih (.loop body stack)).head (enter_iteration body input stack)).tail exit
  | @again carried sigs body input next output tag activation continues later firstIH laterIH =>
    intro final stack
    have restart : Step (.returned (.cons tag next) (.loop body stack)) (.eval (.iteration body next) stack) := by
      change some (State.finishLoop body tag next stack) = some (.eval (.iteration body next) stack)
      simp only [State.finishLoop, continues, ↓reduceIte]
    exact (((firstIH (.loop body stack)).head (enter_iteration body input stack)).tail restart).trans (laterIH stack)

theorem completes_of_returns {job : Job m outs} {output : Tuple m.Val outs}
    (derivation : Returns m job output) : Completes (start job) output :=
  evaluates derivation .halt

theorem runFor_reachable (fuel : Nat) (state : State m final) :
    Relation.ReflTransGen Step state (State.runFor fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
    cases next : state.next with
    | none => rw [State.runFor, next]
    | some target =>
      rw [State.runFor, next]
      exact (ih target).head next

theorem completes_runFor {state : State m final} {fuel : Nat} {output : Tuple m.Val final}
    (result : (State.runFor fuel state).result = some output) : Completes state output := by
  have path := runFor_reachable fuel state
  generalize State.runFor fuel state = reached at result path
  cases reached with
  | eval => cases result
  | returned value stack =>
    cases stack with
    | halt =>
      have same := Option.some.inj (show some value = some output from result)
      exact same ▸ path
    | resume => cases result
    | loop => cases result

theorem no_unsupported (state : State m final) : ¬ state.Unsupported := by
  rintro ⟨stops, result⟩
  cases state with
  | returned value stack =>
    cases stack with
    | halt => cases result
    | resume => cases stops
    | loop => cases value; cases stops
  | eval job stack =>
    cases job with
    | call => cases stops
    | region body => cases body <;> cases stops
    | iteration => cases stops
    | node kind _ _ input =>
      cases kind with
      | theta => cases stops
      | base shape =>
        cases shape with
        | gamma => cases input; cases stops
        | simple instruction =>
          cases instruction with
          | primitive => cases stops
          | apply => cases input; cases stops

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Proofs
