module

public import Mathlib.Data.Nat.Find
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Proofs

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {micro : Nat → State m final} {begin finish : Nat} {next : Entry m}

private theorem advance (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {i : Nat} {source target : State m final} (atSource : micro i = source) (edge : Step source target) :
    micro (i + 1) = target :=
  step_deterministic (steps i) (atSource.symm ▸ edge)

private theorem before_entry {i : Nat} (bounded : i ≤ finish)
    {state : State m final} (actual : micro i = state) (noncall : Entry.ofState state = none)
    (selected : Entry.ofState (micro finish) = some next) : i < finish := by
  by_contra tooLate
  have same : i = finish := by omega
  rw [← same, actual, noncall] at selected
  cases selected

private theorem delimited_slice (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (frame : Stack m ports final) (i count : Nat)
    (within : ∀ offset, offset < count → ¬ Feedback.atReturn frame (micro (i + offset))) :
    ReflTransGen (Feedback.InsideStep frame) (micro i) (micro (i + count)) := by
  induction count with
  | zero => exact .refl
  | succ count ih =>
    exact (ih fun offset smaller => within offset (by omega)).tail
      ⟨steps (i + count), within count (Nat.lt_succ_self _)⟩

private theorem first_return (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {job : Job m ports} {frame : Stack m ports final} (entered : micro begin = .eval job frame) :
    (∃ stop, begin ≤ stop ∧ stop < finish ∧ ∃ value,
      micro stop = .returned value frame ∧ Returns m job value) ∨ BeforeReturn micro begin finish frame := by
  classical
  by_cases found : ∃ offset, begin + offset < finish ∧ Feedback.atReturn frame (micro (begin + offset))
  · let offset := Nat.find found
    obtain ⟨inTime, value, returned⟩ := Nat.find_spec found
    have path := delimited_slice steps frame begin offset
      (fun j smaller observed => Nat.find_min found smaller ⟨by omega, observed⟩)
    rw [entered, returned] at path
    exact .inl ⟨begin + offset, Nat.le_add_right _ _, inTime, value, returned,
      (Feedback.returns_iff_delimited frame).mpr path⟩
  · refine .inr (fun i lower upper observed => found ⟨i - begin, ?_, ?_⟩)
    · simpa only [Nat.add_sub_of_le lower] using upper
    · simpa only [Nat.add_sub_of_le lower] using observed

theorem prefix_of_interval (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (atFinish : Entry.ofState (micro finish) = some next) {job : Job m ports} {stack : Stack m ports final}
    (atBegin : micro begin = .eval job stack) (before : begin < finish)
    (live : BeforeReturn micro begin finish stack) (earlier : EarlierCallsReturn micro begin finish) :
    ∃ pending, Prefix m job next pending ∧ micro finish = next.state (pending.push stack) := by
  classical
  suffices search : ∀ distance start, finish - start = distance → start < finish →
      ∀ {active : Ports (Ty V S)} (job : Job m active) (stack : Stack m active final),
        micro start = .eval job stack →
        BeforeReturn micro start finish stack → EarlierCallsReturn micro start finish →
        ∃ pending, Prefix m job next pending ∧ micro finish = next.state (pending.push stack) from
    search _ begin rfl before job stack atBegin live earlier
  intro distance
  induction distance using Nat.strong_induction_on with
  | ind distance ih =>
    intro start distanceEq before active job stack actual lives completed
    have search {active' : Ports (Ty V S)} {cursor : Nat} {job' : Job m active'} {stack' : Stack m active' final}
        (after : start < cursor) (bound : cursor < finish) (actual' : micro cursor = .eval job' stack')
        (live' : BeforeReturn micro cursor finish stack') :
        ∃ pending, Prefix m job' next pending ∧ micro finish = next.state (pending.push stack') :=
      ih (finish - cursor) (by omega) cursor rfl bound job' stack' actual' live'
        (fun i lower upper => completed i (by omega) upper)
    cases job with
    | call callee arguments =>
      obtain ⟨j, later, sooner, returned⟩ := completed start (Nat.le_refl _) before callee arguments stack actual
      exact False.elim (lives j (Nat.le_of_lt later) sooner returned)
    | iteration body input =>
      let frame := Stack.loop body stack
      let active := Job.region body input (PUnit.unit : Locals m.Val [])
      have entered : micro (start + 1) = .eval active frame :=
        advance steps actual (show Step _ (.eval active frame) from rfl)
      rcases first_return (finish := finish) steps entered with
        ⟨stop, afterEnter, inTime, value, returned, ran⟩ | under
      · cases value with
        | cons tag values =>
          by_cases again : (tag.selector.val == 1) = true
          · have edge : Step (.returned (.cons tag values) frame) (Feedback.restart body stack values) := by
              change some (State.finishLoop body tag values stack) = some (Feedback.restart body stack values)
              rw [State.finishLoop, ite_eq_left again]
              rfl
            have restarted := advance steps returned edge
            have stillBefore := before_entry (by omega) restarted rfl atFinish
            obtain ⟨pending, loop, observed⟩ := search (by omega) stillBefore restarted
              (fun i lower upper => lives i (by omega) upper)
            cases loop with
            | iteration completedFeedback inBody =>
              exact ⟨_, .iteration (completedFeedback.head ⟨tag, ran, again⟩) inBody, observed⟩
          · have edge : Step (.returned (.cons tag values) frame) (.returned values stack) := by
              change some (State.finishLoop body tag values stack) = some (.returned values stack)
              rw [State.finishLoop, ite_eq_right again]
            have exited := advance steps returned edge
            exact False.elim (lives _ (by omega) (before_entry (by omega) exited rfl atFinish) ⟨_, exited⟩)
      · have inTime := before_entry (by omega) entered rfl atFinish
        obtain ⟨pending, inBody, observed⟩ := search (by omega) inTime entered under
        exact ⟨.loop body pending, .iteration .refl inBody, observed⟩
    | region body entry locals =>
      cases body with
      | ret wires =>
        have reached := advance steps actual
          (show Step (.eval (.region (.ret wires) entry locals) stack)
            (.returned (wires.read entry locals) stack) from rfl)
        have within := before_entry (by omega) reached rfl atFinish
        exact False.elim (lives _ (by omega) within ⟨_, reached⟩)
      | bind node children rest =>
        let frame := Stack.resume rest entry locals stack
        let nodeJob := Job.node node.kind node.childSigs children (node.inputs.read entry locals)
        have entered : micro (start + 1) = .eval nodeJob frame :=
          advance steps actual (show Step _ (.eval nodeJob frame) from rfl)
        have inTime := before_entry (by omega) entered rfl atFinish
        rcases first_return (finish := finish) steps entered with
          ⟨stop, afterEnter, returnedBefore, value, returned, ran⟩ | under
        · have resumed : micro (stop + 1) = .eval (.region rest entry (locals.snoc value)) stack :=
            advance steps returned (show Step _ (.eval (.region rest entry (locals.snoc value)) stack) from rfl)
          have stillBefore := before_entry (by omega) resumed rfl atFinish
          obtain ⟨pending, later, observed⟩ := search (by omega) stillBefore resumed
            (fun i lower upper => lives i (by omega) upper)
          exact ⟨pending, .later ran later, observed⟩
        · obtain ⟨pending, inside, observed⟩ := search (by omega) inTime entered under
          exact ⟨.bind rest entry locals pending, .inside inside, observed⟩
    | node kind cs children input =>
      cases kind with
      | theta =>
        have entered := advance steps actual (show Step _ (.eval (.iteration (children (0 : Fin 1)) input) stack) from rfl)
        have inTime := before_entry (by omega) entered rfl atFinish
        obtain ⟨pending, inLoop, observed⟩ := search (by omega) inTime entered
          (fun i lower upper => lives i (by omega) upper)
        exact ⟨pending, .theta inLoop, observed⟩
      | base shape =>
        cases shape with
        | gamma extra =>
          cases input with
          | cons tag inputs =>
            cases tag with
            | control tag =>
              have entered := advance steps actual
                (show Step _ (.eval (.region (children tag) inputs PUnit.unit) stack) from rfl)
              have inTime := before_entry (by omega) entered rfl atFinish
              obtain ⟨pending, inArm, observed⟩ := search (by omega) inTime entered
                (fun i lower upper => lives i (by omega) upper)
              exact ⟨pending, .gamma inArm, observed⟩
        | simple instruction =>
          cases instruction with
          | primitive opcode =>
            have reached := advance steps actual
              (show Step _ (.returned (m.primitive opcode input) stack) from rfl)
            have within := before_entry (by omega) reached rfl atFinish
            exact False.elim (lives _ (by omega) within ⟨_, reached⟩)
          | apply fn =>
            cases input with
            | cons callee args =>
              let selected : Entry m := ⟨fn.results, ⟨fn.args, callee, args⟩⟩
              have entered : micro (start + 1) = selected.state stack :=
                advance steps actual (show Step _ (selected.state stack) from rfl)
              have first : start + 1 = finish := by
                by_contra notFirst
                obtain ⟨i, later, sooner, returned⟩ :=
                  completed (start + 1) (by omega) (by omega) callee args stack entered
                exact lives i (by omega) sooner returned
              have observed : micro finish = selected.state stack := first ▸ entered
              have same : selected = next := Option.some.inj
                ((show Entry.ofState (selected.state stack) = some selected from rfl).symm.trans
                  ((congrArg Entry.ofState observed).symm.trans atFinish))
              subst next
              exact ⟨.empty, .apply callee args, observed⟩

theorem entry_of_theta_interval (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {caller : Entry m} {stack : Stack m caller.results final} {nextStack : Stack m next.results final}
    (atCaller : micro begin = caller.state stack) (atCallee : micro finish = next.state nextStack)
    (rising : begin < finish) (live : BeforeReturn micro (begin + 1) finish stack)
    (earlier : EarlierCallsReturn micro (begin + 1) finish) :
    ∃ pending, Prefix m caller.openBody next pending ∧ pending.push stack = nextStack := by
  have opened : micro (begin + 1) = .eval caller.openBody stack :=
    advance steps atCaller (show Step _ (.eval caller.openBody stack) from rfl)
  have selected : Entry.ofState (micro finish) = some next := by
    rw [atCallee]
    cases next with
    | mk results activation => cases activation; rfl
  have before := before_entry (Nat.succ_le_of_lt rising) opened rfl selected
  obtain ⟨pending, independent, observed⟩ := prefix_of_interval steps selected opened before live earlier
  have same := observed.symm.trans atCallee
  exact ⟨pending, independent, by cases same; rfl⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Proofs
