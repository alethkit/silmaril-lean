module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Observation

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {micro : Nat → Config m σ final} {begin : Nat}

private theorem feedback_earlier {later : Nat} (found : HasFeedback primitives micro later) (lower : begin ≤ later) :
    HasFeedback primitives micro begin := by
  obtain ⟨target, parent, positions, inputs, after, trace⟩ := found
  exact ⟨target, parent, positions, inputs, lower.trans after, trace⟩

private theorem feedback_from_node (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {args : Ports (Ty V S)} {kind : NestedTheta.Kind (Instruction Op) args ports}
    {cs : Fin kind.arity → List (Ports (Ty V S))} {children : Bodies kind cs}
    {input : Tuple m.Val args} {stack : Stack m ports final} {store : σ}
    (search : ∀ (child : Fin kind.arity) entry i state (frame : Stack m kind.exit final),
      micro i = ⟨.eval (.region (children child) entry PUnit.unit) frame, state⟩ →
      LiveFrom micro i frame → (∀ j, i ≤ j → ¬ NonreturningCallAt micro j) → HasFeedback primitives micro i)
    (entered : micro begin = ⟨.eval (.node kind cs children input) stack, store⟩)
    (live : LiveFrom micro begin stack) (returns : ∀ i, begin ≤ i → ¬ NonreturningCallAt micro i) :
    HasFeedback primitives micro begin := by
  cases kind with
  | theta =>
    have started : micro (begin + 1) = (Feedback.Restart.mk _ _ (children (0 : Fin 1)) (input, store)).config stack :=
      advance steps entered (.of_next_some rfl)
    rcases loop_or_live_body steps started (fun i lower => live i (by omega)) with
      feedback | ⟨i, values, after, active, bodyLive⟩
    · exact feedback_earlier feedback (by omega)
    · exact feedback_earlier
        (search (0 : Fin 1) values.1 i values.2 _ active bodyLive (fun j lower => returns j (by omega))) (by omega)
  | base shape =>
    cases shape with
    | gamma extra =>
      cases input with
      | cons tag arguments =>
        cases tag with
        | control selected =>
          have inArm : micro (begin + 1) =
              ⟨.eval (.region (children selected) arguments PUnit.unit) stack, store⟩ :=
            advance steps entered (.of_next_some rfl)
          exact feedback_earlier
            (search selected arguments _ store stack inArm (fun j lower => live j (by omega))
              (fun j lower => returns j (by omega))) (by omega)
    | simple instruction =>
      cases instruction with
      | primitive opcode =>
        have edge := steps begin
        rw [entered] at edge
        change micro (begin + 1) ∈ ((primitives.step opcode input).run store).map
          (fun (value, state) => Config.mk (.returned value stack) state) at edge
        obtain ⟨⟨value, _⟩, _, returned⟩ := (_root_.Part.mem_map_iff _).mp edge
        exact False.elim (live _ (by omega) ⟨value, (congrArg Config.control returned).symm⟩)
      | apply fn =>
        cases input with
        | cons callee arguments =>
          let call : Entry m σ := ⟨⟨fn.results, ⟨fn.args, callee, arguments⟩⟩, store⟩
          have child : micro (begin + 1) = call.config stack :=
            advance steps entered (.of_next_some rfl)
          exact False.elim (returns _ (by omega) ⟨call, stack, child, fun i lower => live i (by omega)⟩)

private theorem feedback_from_region (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {args : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
    (body : NestedTheta.Term (Instruction Op) args past sigs ports) :
    ∀ input locals state (stack : Stack m ports final) (i : Nat),
      micro i = ⟨.eval (.region body input locals) stack, state⟩ → LiveFrom micro i stack →
      (∀ j, i ≤ j → ¬ NonreturningCallAt micro j) → HasFeedback primitives micro i := by
  induction body with
  | ret wires =>
    intro input locals state stack i entered live _
    have returned : micro (i + 1) = ⟨.returned (wires.read input locals) stack, state⟩ :=
      advance steps entered (.of_next_some rfl)
    exact False.elim (live _ (by omega) ⟨_, congrArg Config.control returned⟩)
  | bind node children rest childIH restIH =>
    intro input locals state stack i entered lives returns
    let frame := Stack.resume rest input locals stack
    let active := Job.node node.kind node.childSigs children (node.inputs.read input locals)
    have atNode : micro (i + 1) = ⟨.eval active frame, state⟩ :=
      advance steps entered (.of_next_some rfl)
    rcases return_or_live steps atNode with ⟨stop, after, value, returned, _⟩ | live
    · have resumed : micro (stop + 1) =
          ⟨.eval (.region rest input (locals.snoc value)) stack, (micro stop).store⟩ :=
        advance steps returned (.of_next_some rfl)
      exact feedback_earlier (restIH input (locals.snoc value) (micro stop).store stack _ resumed
        (fun j lower => lives j (by omega)) (fun j lower => returns j (by omega))) (by omega)
    · exact feedback_earlier
        (feedback_from_node steps (fun child entry j store stk => childIH child entry PUnit.unit store stk j)
          atNode live (fun j lower => returns j (by omega))) (by omega)

theorem feedback_of_live (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {caller : Entry m σ} {base : Stack m caller.call.results final}
    (entered : micro begin = caller.config base) (live : LiveFrom micro begin base)
    (returns : ∀ i, begin < i → ¬ NonreturningCallAt micro i) :
    HasFeedback primitives micro (begin + 1) := by
  have opened : micro (begin + 1) = ⟨.eval caller.call.openBody base, caller.store⟩ :=
    advance steps entered (.of_next_some rfl)
  let closure := resolve m caller.call.activation.callee
  exact feedback_from_region steps closure.body.toTerm (Closure.enter Op closure caller.call.activation.arguments)
    PUnit.unit caller.store base _ opened (fun j lower => live j (by omega)) (fun j lower => returns j (by omega))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Proofs
