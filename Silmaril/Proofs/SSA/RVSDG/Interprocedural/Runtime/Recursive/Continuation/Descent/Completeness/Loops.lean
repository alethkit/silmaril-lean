module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Calls

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {micro : Nat → State m final} {begin : Nat}

private theorem advance (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {source target : State m final} (entered : micro begin = source) (edge : Step source target) :
    micro (begin + 1) = target :=
  step_deterministic (steps begin) (entered.symm ▸ edge)

private theorem feedback_earlier {later : Nat} (found : HasFeedback micro later) (lower : begin ≤ later) :
    HasFeedback micro begin := by
  obtain ⟨i, carried, sigs, body, parent, inputs, positions, after, live, trace⟩ := found
  exact ⟨i, carried, sigs, body, parent, inputs, positions, lower.trans after, live, trace⟩

/-- A live θ either has infinitely many completed feedback iterations
or reaches a particular body that stays active. -/
private theorem loop_or_live_body (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
    {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
    {input : Tuple m.Val carried} {parent : Stack m carried final}
    (entered : micro begin = Feedback.restart body parent input) (live : LiveFrom micro begin parent) :
    HasFeedback micro begin ∨ ∃ i current, begin < i ∧
      micro i = .eval (.region body current (PUnit.unit : Locals m.Val [])) (.loop body parent) ∧
      LiveFrom micro i (.loop body parent) := by
  let shifted (i : Nat) := micro (begin + i)
  have initial : shifted 0 = Feedback.restart body parent input := by simpa only [shifted, Nat.add_zero]
  have advances (i : Nat) : Step (shifted i) (shifted (i + 1)) := by
    simpa only [shifted, Nat.add_assoc] using steps (begin + i)
  have stays : Feedback.Divergence.StaysInLoop body parent shifted := by
    intro i tag carried returned
    by_contra stops
    have exit : Step (.returned (.cons tag carried) (.loop body parent)) (.returned carried parent) := by
      change some (State.finishLoop body tag carried parent) = some (.returned carried parent)
      rw [State.finishLoop, ite_eq_right stops]
    exact live (begin + i + 1) (by omega) ⟨_, advance steps returned exit⟩
  rcases (Feedback.Divergence.stays_iff_decomposes advances initial).mp stays with
    ⟨inputs, positions, _, trace⟩ | ⟨last, _, forever⟩
  · exact .inl ⟨begin, carried, sigs, body, parent, inputs, positions, Nat.le_refl _, live, trace⟩
  · have entersBody := (forever.bodySuffix advances).1
    refine .inr ⟨begin + last.1 + 1, last.2, by omega, ?_, ?_⟩
    · simpa only [shifted, Nat.add_assoc] using entersBody
    · intro i after
      have within : last.1 < i - begin := by omega
      have atBody := forever.2 (i - begin) within
      simpa only [shifted, Nat.add_sub_of_le (by omega : begin ≤ i)] using atBody

private theorem loop_from_node (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {args : Ports (Ty V S)} {kind : NestedTheta.Kind (Instruction Op) args ports}
    {cs : Fin kind.arity → List (Ports (Ty V S))} {children : Bodies kind cs}
    {input : Tuple m.Val args} {stack : Stack m ports final}
    (search : ∀ (child : Fin kind.arity) entry i (frame : Stack m kind.exit final),
      micro i = .eval (.region (children child) entry (PUnit.unit : Locals m.Val [])) frame →
      LiveFrom micro i frame → (∀ j, i ≤ j → ¬ NonreturningCallAt micro j) → HasFeedback micro i)
    (entered : micro begin = .eval (.node kind cs children input) stack)
    (live : LiveFrom micro begin stack) (returns : ∀ i, begin ≤ i → ¬ NonreturningCallAt micro i) :
    HasFeedback micro begin := by
  cases kind with
  | theta =>
    have started : micro (begin + 1) = Feedback.restart (children (0 : Fin 1)) stack input :=
      advance steps entered (show Step _ (Feedback.restart (children (0 : Fin 1)) stack input) from rfl)
    rcases loop_or_live_body steps started (fun i lower => live i (by omega)) with
      feedback | ⟨i, values, after, active, bodyLive⟩
    · exact feedback_earlier feedback (by omega)
    · exact feedback_earlier
        (search (0 : Fin 1) values i _ active bodyLive (fun j lower => returns j (by omega))) (by omega)
  | base shape =>
    cases shape with
    | gamma extra =>
      cases input with
      | cons tag arguments =>
        cases tag with
        | control selected =>
          have inArm : micro (begin + 1) =
              .eval (.region (children selected) arguments PUnit.unit) stack :=
            advance steps entered (show Step _ (.eval (.region (children selected) arguments PUnit.unit) stack) from rfl)
          exact feedback_earlier
            (search selected arguments _ stack inArm (fun j lower => live j (by omega))
              (fun j lower => returns j (by omega))) (by omega)
    | simple instruction =>
      cases instruction with
      | primitive opcode =>
        have returned : micro (begin + 1) = .returned (m.primitive opcode input) stack :=
          advance steps entered (show Step _ (.returned (m.primitive opcode input) stack) from rfl)
        exact False.elim (live _ (by omega) ⟨_, returned⟩)
      | apply fn =>
        cases input with
        | cons callee arguments =>
          let call : Entry m := ⟨fn.results, ⟨fn.args, callee, arguments⟩⟩
          have child : micro (begin + 1) = call.state stack :=
            advance steps entered (show Step _ (call.state stack) from rfl)
          exact False.elim (returns _ (by omega) ⟨call, stack, child, fun i lower => live i (by omega)⟩)

private theorem loop_from_region (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {args : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
    (body : NestedTheta.Term (Instruction Op) args past sigs ports) :
    ∀ input locals (stack : Stack m ports final) (i : Nat),
      micro i = .eval (.region body input locals) stack → LiveFrom micro i stack →
      (∀ j, i ≤ j → ¬ NonreturningCallAt micro j) → HasFeedback micro i := by
  induction body with
  | ret wires =>
    intro input locals stack i entered live _
    have returned : micro (i + 1) = .returned (wires.read input locals) stack :=
      advance steps entered (show Step _ (.returned (wires.read input locals) stack) from rfl)
    exact False.elim (live _ (by omega) ⟨_, returned⟩)
  | bind node children rest childIH restIH =>
    intro input locals stack i entered lives returns
    let frame := Stack.resume rest input locals stack
    let active := Job.node node.kind node.childSigs children (node.inputs.read input locals)
    have atNode : micro (i + 1) = .eval active frame :=
      advance steps entered (show Step _ (.eval active frame) from rfl)
    rcases return_or_live atNode with ⟨stop, after, value, returned⟩ | live
    · have resumed : micro (stop + 1) = .eval (.region rest input (locals.snoc value)) stack :=
        advance steps returned (show Step _ (.eval (.region rest input (locals.snoc value)) stack) from rfl)
      exact feedback_earlier (restIH input (locals.snoc value) stack _ resumed
        (fun j lower => lives j (by omega)) (fun j lower => returns j (by omega))) (by omega)
    · exact feedback_earlier (loop_from_node steps
        (fun child entry j stk => childIH child entry PUnit.unit stk j) atNode live
        (fun j lower => returns j (by omega))) (by omega)

theorem split_live (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {caller : Entry m} {base : Stack m caller.results final}
    (entered : micro begin = caller.state base) (live : LiveFrom micro begin base) :
    HasFirstChild caller base micro begin ∨
      (∀ i, begin < i → ¬ NonreturningCallAt micro i) ∧ HasFeedback micro (begin + 1) := by
  classical
  by_cases child : ∃ i, begin < i ∧ NonreturningCallAt micro i
  · exact .inl (first_child steps entered live child)
  · have closed (i : Nat) (later : begin < i) : ¬ NonreturningCallAt micro i :=
      fun observed => child ⟨i, later, observed⟩
    have opened : micro (begin + 1) = .eval caller.openBody base :=
      advance steps entered (show Step _ (.eval caller.openBody base) from rfl)
    let closure := resolve m caller.activation.callee
    exact .inr ⟨closed, loop_from_region steps closure.body.toTerm (Closure.enter Op closure caller.activation.arguments)
      PUnit.unit base _ opened (fun j lower => live j (by omega)) (fun j lower => closed j (by omega))⟩

theorem split_start {caller : Entry m} {micro : Nat → State m caller.results}
    (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (entered : micro 0 = caller.state (.halt : Stack m caller.results caller.results)) :
    HasFirstChild caller .halt micro 0 ∨
      (∀ i, 0 < i → ¬ NonreturningCallAt micro i) ∧ HasFeedback micro 1 := by
  apply split_live steps entered
  rintro i _ ⟨_, returned⟩
  have edge := steps i
  rw [returned] at edge
  cases edge

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Proofs
