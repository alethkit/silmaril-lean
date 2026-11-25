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

private def observes (output : Tuple m.Val final) : State m final → Prop
  | .eval job stack => ∃ value, Returns m job value ∧ accepts stack value output
  | .returned value stack => accepts stack value output

private def instructionReturns {ins : Ports (Ty V S)} (output : Tuple m.Val outs)
    (instruction : Instruction Op ins outs) : Tuple m.Val ins → Prop :=
  match instruction with
  | .primitive _ => fun _ => True
  | .apply _ => fun
    | .cons callee arguments => Returns m (.call callee arguments) output

private def applicationReturns (output : Tuple m.Val outs) : Job m outs → Prop
  | .node kind _ _ input =>
    match kind with
    | .base shape =>
      match shape with
      | .simple instruction => instructionReturns output instruction input
      | .gamma _ => True
    | .theta _ => True
  | _ => True

private theorem application_returns {job : Job m outs} {output : Tuple m.Val outs}
    (returned : Returns m job output) : applicationReturns output job := by
  cases returned with
  | apply invocation => exact invocation
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
        change none = some target at edge
        cases edge
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
                exact ⟨_, application_returns ran, rest⟩
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
    | iteration =>
      change none = some target at edge
      cases edge

private theorem observes_trace {source target : State m final} (path : Path source target)
    (output : Tuple m.Val final) : observes output source ↔ observes output target := by
  induction path with
  | refl => rfl
  | tail _ edge ih => exact ih.trans (observes_step edge output)

theorem completes_sound {job : Job m outs} {output : Tuple m.Val outs}
    (complete : Completes (start job) output) : Returns m job output := by
  obtain ⟨_, returned, rfl⟩ := (observes_trace complete output).mpr (show output = output from rfl)
  exact returned

private def Progress (source target : State m final) : Prop :=
  Path source target ∨ ∃ stuck, Path source stuck ∧ stuck.Unsupported

private theorem Progress.prepend {source middle target : State m final}
    (heading : Path source middle) (later : Progress middle target) : Progress source target := by
  rcases later with done | ⟨stuck, path, stops⟩
  · exact .inl (heading.trans done)
  · exact .inr ⟨stuck, heading.trans path, stops⟩

private theorem blocked {state target : State m final} (unsupported : state.Unsupported) :
    Progress state target := .inr ⟨state, .refl, unsupported⟩

private theorem progress {job : Job m outs} {value : Tuple m.Val outs} (derivation : Returns m job value) :
    ∀ {final : Ports (Ty V S)} (stack : Stack m outs final),
      Progress (.eval job stack) (.returned value stack) := by
  induction derivation with
  | call _ ih => intro final stack; exact (ih stack).prepend (.single rfl)
  | ret => intro final stack; exact .inl (.single rfl)
  | @bind args head outs past tail node children rest entry locals value output first more firstIH restIH =>
    intro final stack
    let resume := Stack.resume rest entry locals stack
    let nodeJob := Job.node node.kind node.childSigs children (node.inputs.read entry locals)
    have enters : Step (.eval (.region (.bind node children rest) entry locals) stack) (.eval nodeJob resume) := rfl
    rcases firstIH resume with done | ⟨stuck, path, stops⟩
    · have resumed : Step (.returned value resume) (.eval (.region rest entry (locals.snoc value)) stack) := rfl
      exact (restIH stack).prepend ((done.head enters).tail resumed)
    · exact .inr ⟨stuck, path.head enters, stops⟩
  | primitive => intro final stack; exact .inl (.single rfl)
  | apply _ ih => intro final stack; exact (ih stack).prepend (.single rfl)
  | gamma _ ih => intro final stack; exact (ih stack).prepend (.single rfl)
  | theta => intro final stack; exact blocked ⟨rfl, rfl⟩
  | stop => intro final stack; exact blocked ⟨rfl, rfl⟩
  | again => intro final stack; exact blocked ⟨rfl, rfl⟩

theorem returns_or_unsupported {job : Job m outs} {output : Tuple m.Val outs}
    (derivation : Returns m job output) :
    Completes (start job) output ∨
      ∃ state, Relation.ReflTransGen Step (start job) state ∧ state.Unsupported :=
  progress derivation .halt

theorem completes_of_returns {job : Job m outs} {output : Tuple m.Val outs}
    (admitted : Admitted (start job)) (derivation : Returns m job output) :
    Completes (start job) output := by
  rcases returns_or_unsupported derivation with complete | ⟨_, path, stuck⟩
  · exact complete
  · exact False.elim (admitted _ path stuck)

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

theorem admitted_of_completes {state : State m final} {output : Tuple m.Val final}
    (complete : Completes state output) : Admitted state := by
  intro reached path unsupported
  have deterministic : Relator.RightUnique (Step (m := m) (outs := final)) :=
    fun {_ _ _} e₁ e₂ => Option.some.inj (e₁.symm.trans e₂)
  rcases Relation.ReflTransGen.total_of_right_unique deterministic path complete with toReturn | fromReturn
  · rcases toReturn.cases_head with same | ⟨_, step, _⟩
    · rw [same] at unsupported
      cases unsupported.2
    · cases unsupported.1.symm.trans step
  · rcases fromReturn.cases_head with same | ⟨_, step, _⟩
    · rw [← same] at unsupported
      cases unsupported.2
    · change none = some _ at step
      cases step

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Proofs
