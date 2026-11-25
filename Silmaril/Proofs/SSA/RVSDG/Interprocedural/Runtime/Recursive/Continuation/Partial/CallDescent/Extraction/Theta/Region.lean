module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Observation

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {micro : Nat → Config m σ final} {begin : Nat}

private theorem feedback_before {other : Ports (Ty V S)} {later : Nat}
    {job : Job m ports} {stack : Stack m ports final} {store : σ}
    {nextJob : Job m other} {nextStack : Stack m other final} {nextStore : σ}
    (found : ReachesFeedback primitives micro later nextJob nextStore nextStack) (lower : begin ≤ later)
    (wrap : ∀ (target : Feedback.Restart m σ) (pending : Descent.Pending m target.carried other),
      Feedback.Reaches primitives nextJob nextStore target pending →
      ∃ outer : Descent.Pending m target.carried ports,
        Feedback.Reaches primitives job store target outer ∧ outer.push stack = pending.push nextStack) :
    ReachesFeedback primitives micro begin job store stack := by
  obtain ⟨target, pending, positions, inputs, after, reached, observed⟩ := found
  obtain ⟨outer, reached, frames⟩ := wrap target pending reached
  exact ⟨target, outer, positions, inputs, lower.trans after, reached, frames.symm ▸ observed⟩

private theorem feedback_from_node (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {args : Ports (Ty V S)} {kind : NestedTheta.Kind (Instruction Op) args ports}
    {cs : Fin kind.arity → List (Ports (Ty V S))} {children : Bodies kind cs}
    {input : Tuple m.Val args} {stack : Stack m ports final} {store : σ}
    (search : ∀ (child : Fin kind.arity) entry i state (frame : Stack m kind.exit final),
      micro i = ⟨.eval (.region (children child) entry PUnit.unit) frame, state⟩ →
      LiveFrom micro i frame → (∀ j, i ≤ j → ¬ NonreturningCallAt micro j) →
        ReachesFeedback primitives micro i (.region (children child) entry PUnit.unit) state frame)
    (entered : micro begin = ⟨.eval (.node kind cs children input) stack, store⟩)
    (live : LiveFrom micro begin stack) (returns : ∀ i, begin ≤ i → ¬ NonreturningCallAt micro i) :
    ReachesFeedback primitives micro begin (.node kind cs children input) store stack := by
  cases kind with
  | theta =>
    have started : micro (begin + 1) = (Feedback.Restart.mk _ _ (children (0 : Fin 1)) (input, store)).config stack :=
      advance steps entered (.of_next_some rfl)
    rcases loop_or_live_body steps started (fun i lower => live i (by omega)) with
      ⟨positions, inputs, atStart, feedback⟩ | ⟨i, values, after, completed, active, bodyLive⟩
    · let target : Feedback.Restart m σ := ⟨ports, cs (0 : Fin 1), children (0 : Fin 1), (input, store)⟩
      have independent : Feedback.Reaches primitives (.node (.theta ports) cs children input) store target .empty :=
        .theta (.restart (input := (input, store)) (current := (input, store)) .refl)
      refine ⟨target, .empty, positions, inputs, ?_, independent, feedback⟩
      rw [atStart]
      omega
    · exact feedback_before
        (search (0 : Fin 1) values.1 i values.2 _ active bodyLive (fun j lower => returns j (by omega))) (by omega)
        (fun _ pending reached => ⟨.loop (children (0 : Fin 1)) pending, .theta (.iteration completed reached), rfl⟩)
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
          exact feedback_before
            (search selected arguments _ store stack inArm (fun j lower => live j (by omega))
              (fun j lower => returns j (by omega))) (by omega)
            (fun _ pending reached => ⟨pending, .gamma reached, rfl⟩)
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
      (∀ j, i ≤ j → ¬ NonreturningCallAt micro j) →
      ReachesFeedback primitives micro i (.region body input locals) state stack := by
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
    rcases return_or_live steps atNode with ⟨stop, after, value, returned, ran⟩ | live
    · have resumed : micro (stop + 1) =
          ⟨.eval (.region rest input (locals.snoc value)) stack, (micro stop).store⟩ :=
        advance steps returned (.of_next_some rfl)
      exact feedback_before (restIH input (locals.snoc value) (micro stop).store stack _ resumed
        (fun j lower => lives j (by omega)) (fun j lower => returns j (by omega))) (by omega)
        (fun _ pending reached => ⟨pending, .later ran reached, rfl⟩)
    · exact feedback_before
        (feedback_from_node steps (fun child entry j store stk => childIH child entry PUnit.unit store stk j)
          atNode live (fun j lower => returns j (by omega))) (by omega)
        (fun _ pending reached => ⟨.bind rest input locals pending, .inside reached, rfl⟩)

theorem reaches_feedback_of_live (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {caller : Entry m σ} {base : Stack m caller.call.results final}
    (entered : micro begin = caller.config base) (live : LiveFrom micro begin base)
    (returns : ∀ i, begin < i → ¬ NonreturningCallAt micro i) :
    ReachesFeedback primitives micro (begin + 1) caller.call.openBody caller.store base := by
  have opened : micro (begin + 1) = ⟨.eval caller.call.openBody base, caller.store⟩ :=
    advance steps entered (.of_next_some rfl)
  let closure := resolve m caller.call.activation.callee
  exact feedback_from_region steps closure.body.toTerm (Closure.enter Op closure caller.call.activation.arguments)
    PUnit.unit caller.store base _ opened (fun j lower => live j (by omega)) (fun j lower => returns j (by omega))

theorem feedback_of_live (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {caller : Entry m σ} {base : Stack m caller.call.results final}
    (entered : micro begin = caller.config base) (live : LiveFrom micro begin base)
    (returns : ∀ i, begin < i → ¬ NonreturningCallAt micro i) :
    HasFeedback primitives micro (begin + 1) := by
  obtain ⟨target, pending, positions, inputs, lower, _, observed⟩ :=
    reaches_feedback_of_live steps entered live returns
  exact ⟨target, pending.push base, positions, inputs, lower, observed⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Proofs
