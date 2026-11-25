module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {micro : Nat → State m final} {begin finish : Nat} {target : Restart m}

private theorem advance (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {i : Nat} {source result : State m final} (atSource : micro i = source) (edge : Step source result) :
    micro (i + 1) = result :=
  step_deterministic (steps i) (atSource.symm ▸ edge)

private theorem at_checkpoint {job : Job m ports} {stack : Stack m ports final}
    {targetStack : Stack m target.carried final} (same : State.eval job stack = target.state targetStack) :
    ∃ pending, Reaches m job target pending ∧ pending.push stack = targetStack := by
  cases target with
  | mk carried sigs body input =>
    change State.eval job stack = State.eval (.iteration body input) targetStack at same
    cases same
    exact ⟨.empty, .restart .refl, rfl⟩

private theorem return_before_target {i : Nat} {value : Tuple m.Val ports} {stack : Stack m ports final}
    {targetStack : Stack m target.carried final} (inTime : i ≤ finish)
    (returned : micro i = .returned value stack) (selected : micro finish = target.state targetStack) :
    i < finish := by
  apply lt_of_le_of_ne inTime
  intro same
  rw [same] at returned
  have impossible := returned.symm.trans selected
  cases target
  cases impossible

theorem reaches_of_interval (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {job : Job m ports} {stack : Stack m ports final} {targetStack : Stack m target.carried final}
    (opened : micro begin = .eval job stack) (selected : micro finish = target.state targetStack)
    (ordered : begin ≤ finish) (live : BeforeReturn micro begin finish stack)
    (earlier : EarlierCallsReturn micro begin finish) :
    ∃ pending, Reaches m job target pending ∧ pending.push stack = targetStack := by
  suffices search : ∀ distance start, finish - start = distance → start ≤ finish →
      ∀ {active : Ports (Ty V S)} (job : Job m active) (stack : Stack m active final),
        micro start = .eval job stack →
        BeforeReturn micro start finish stack → EarlierCallsReturn micro start finish →
        ∃ pending, Reaches m job target pending ∧ pending.push stack = targetStack from
    search _ begin rfl ordered job stack opened live earlier
  intro distance
  induction distance using Nat.strong_induction_on with
  | ind distance ih =>
    intro start distanceEq inTime active job stack observed lives closed
    by_cases atFinish : start = finish
    · rw [atFinish] at observed
      exact at_checkpoint (observed.symm.trans selected)
    have strict : start < finish := lt_of_le_of_ne inTime atFinish
    have search {other : Ports (Ty V S)} {cursor : Nat} {next : Job m other} {frame : Stack m other final}
        (after : start < cursor) (bound : cursor ≤ finish) (entered : micro cursor = .eval next frame)
        (inside : BeforeReturn micro cursor finish frame) :
        ∃ pending, Reaches m next target pending ∧ pending.push frame = targetStack :=
      ih (finish - cursor) (by omega) cursor rfl bound next frame entered inside
        (fun i lower upper => closed i (by omega) upper)
    cases job with
    | call callee arguments =>
      obtain ⟨i, after, before, returned⟩ := closed start (Nat.le_refl _) strict callee arguments stack observed
      exact False.elim (lives i (by omega) before returned)
    | region body entry locals =>
      cases body with
      | ret wires =>
        have returned : micro (start + 1) = .returned (wires.read entry locals) stack :=
          advance steps observed (show Step _ (.returned (wires.read entry locals) stack) from rfl)
        exact False.elim (lives _ (by omega) (return_before_target (by omega) returned selected) ⟨_, returned⟩)
      | bind node children rest =>
        let frame := Stack.resume rest entry locals stack
        let nodeJob := Job.node node.kind node.childSigs children (node.inputs.read entry locals)
        have entered : micro (start + 1) = .eval nodeJob frame :=
          advance steps observed (show Step _ (.eval nodeJob frame) from rfl)
        rcases Feedback.first_return_before (finish := finish) steps entered with
          ⟨stop, after, before, value, returned, ran⟩ | inside
        · have resumed : micro (stop + 1) = .eval (.region rest entry (locals.snoc value)) stack :=
            advance steps returned (show Step _ (.eval (.region rest entry (locals.snoc value)) stack) from rfl)
          obtain ⟨pending, reached, frames⟩ := search (by omega) (by omega) resumed
            (fun i lower upper => lives i (by omega) upper)
          exact ⟨pending, .later ran reached, frames⟩
        · obtain ⟨pending, reached, frames⟩ := search (by omega) (by omega) entered inside
          exact ⟨.bind rest entry locals pending, .inside reached, frames⟩
    | node kind cs children input =>
      cases kind with
      | theta =>
        have entered : micro (start + 1) = .eval (.iteration (children (0 : Fin 1)) input) stack :=
          advance steps observed (show Step _ (.eval (.iteration (children (0 : Fin 1)) input) stack) from rfl)
        obtain ⟨pending, reached, frames⟩ := search (by omega) (by omega) entered
          (fun i lower upper => lives i (by omega) upper)
        exact ⟨pending, .theta reached, frames⟩
      | base shape =>
        cases shape with
        | gamma extra =>
          cases input with
          | cons tag inputs =>
            cases tag with
            | control tag =>
              have entered := advance steps observed
                (show Step _ (.eval (.region (children tag) inputs PUnit.unit) stack) from rfl)
              obtain ⟨pending, reached, frames⟩ := search (by omega) (by omega) entered
                (fun i lower upper => lives i (by omega) upper)
              exact ⟨pending, .gamma reached, frames⟩
        | simple instruction =>
          cases instruction with
          | primitive opcode =>
            have returned : micro (start + 1) = .returned (m.primitive opcode input) stack :=
              advance steps observed (show Step _ (.returned (m.primitive opcode input) stack) from rfl)
            exact False.elim (lives _ (by omega) (return_before_target (by omega) returned selected) ⟨_, returned⟩)
          | apply fn =>
            cases input with
            | cons callee arguments =>
              have entered := advance steps observed (show Step _ (.eval (.call callee arguments) stack) from rfl)
              obtain ⟨_, impossible, _⟩ := search (by omega) (by omega) entered
                (fun i lower upper => lives i (by omega) upper)
              cases impossible
    | iteration body input =>
      let frame := Stack.loop body stack
      have entered : micro (start + 1) = .eval (.region body input PUnit.unit) frame :=
        advance steps observed (show Step _ (.eval (.region body input PUnit.unit) frame) from rfl)
      rcases Feedback.first_return_before (finish := finish) steps entered with
        ⟨stop, after, before, returned, atReturn, ran⟩ | inside
      · cases returned with
        | cons tag values =>
          by_cases again : (tag.selector.val == 1) = true
          · have edge : Step (.returned (.cons tag values) frame) (Feedback.restart body stack values) := by
              change some (State.finishLoop body tag values stack) = some (Feedback.restart body stack values)
              rw [State.finishLoop, ite_eq_left again]
              rfl
            have restarted := advance steps atReturn edge
            obtain ⟨pending, reached, frames⟩ := search (by omega) (by omega) restarted
              (fun i lower upper => lives i (by omega) upper)
            have completed : Feedback.Iteration body input values := ⟨tag, ran, again⟩
            cases reached with
            | restart rest => exact ⟨_, .restart (rest.head completed), frames⟩
            | iteration rest active => exact ⟨_, .iteration (rest.head completed) active, frames⟩
          · have edge : Step (.returned (.cons tag values) frame) (.returned values stack) := by
              change some (State.finishLoop body tag values stack) = some (.returned values stack)
              rw [State.finishLoop, ite_eq_right again]
            have exited := advance steps atReturn edge
            exact False.elim (lives _ (by omega) (return_before_target (by omega) exited selected) ⟨_, exited⟩)
      · obtain ⟨pending, reached, frames⟩ := search (by omega) (by omega) entered inside
        exact ⟨.loop body pending, .iteration .refl reached, frames⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Proofs
