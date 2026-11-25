module

public import Mathlib.Data.Nat.Find
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Proofs

open Descent (BeforeReturn EarlierCallsReturn)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {micro : Nat → Config m σ final} {begin finish : Nat}
variable {next : Entry m σ}

private def entryOf (config : Config m σ final) : Option (Entry m σ) :=
  (Descent.Entry.ofState config.control).map (fun call => ⟨call, config.store⟩)

private theorem at_control {config : Config m σ final} {control : State m final}
    (actual : config.control = control) : config = ⟨control, config.store⟩ := by
  cases config
  cases actual
  rfl

private theorem advance {i : Nat} {source target : Config m σ final} (actual : micro i = source)
    (observed : Step primitives (micro i) (micro (i + 1))) (edge : Step primitives source target) :
    micro (i + 1) = target :=
  _root_.Part.mem_unique observed (actual.symm ▸ edge)

private theorem before_entry {i : Nat} (bounded : i ≤ finish) {config : Config m σ final}
    (actual : micro i = config) (noncall : entryOf config = none) (selected : entryOf (micro finish) = some next) :
    i < finish := by
  by_contra tooLate
  have same : i = finish := by omega
  rw [← same, actual, noncall] at selected
  cases selected

private theorem delimited_slice (frame : Stack m ports final) (count : Nat)
    (steps : ∀ offset, offset < count → Step primitives (micro (begin + offset)) (micro (begin + offset + 1)))
    (within : ∀ offset, offset < count → ¬ Continuation.Feedback.atReturn frame (micro (begin + offset)).control) :
    ReflTransGen (InsideStep primitives frame) (micro begin) (micro (begin + count)) := by
  induction count with
  | zero => exact .refl
  | succ count ih =>
    exact (ih (fun offset smaller => steps offset (by omega)) (fun offset smaller => within offset (by omega))).tail
      ⟨steps count (Nat.lt_succ_self _), within count (Nat.lt_succ_self _)⟩

private theorem first_return
    (steps : ∀ i, begin ≤ i → i < finish → Step primitives (micro i) (micro (i + 1)))
    {job : Job m ports} {frame : Stack m ports final} {store : σ} (entered : micro begin = ⟨.eval job frame, store⟩) :
    (∃ stop, begin ≤ stop ∧ stop < finish ∧ ∃ value,
      (micro stop).control = .returned value frame ∧ Eval primitives job store (.returned value (micro stop).store)) ∨
      BeforeReturn (fun i => (micro i).control) begin finish frame := by
  classical
  by_cases found : ∃ offset, begin + offset < finish ∧
      Continuation.Feedback.atReturn frame (micro (begin + offset)).control
  · let offset := Nat.find found
    obtain ⟨inTime, value, returned⟩ := Nat.find_spec found
    have path := delimited_slice (begin := begin) frame offset
      (fun i smaller => steps (begin + i) (by omega) (by omega))
      (fun i smaller observed => Nat.find_min found smaller ⟨by omega, observed⟩)
    have exactPath : ReflTransGen (InsideStep primitives frame) ⟨.eval job frame, store⟩
        ⟨.returned value frame, (micro (begin + offset)).store⟩ :=
      entered ▸ at_control returned ▸ path
    exact .inl ⟨_, Nat.le_add_right _ _, inTime, value, returned, returns_of_delimited frame exactPath⟩
  · refine .inr (fun i lower upper observed => found ⟨i - begin, ?_, ?_⟩)
    · simpa only [Nat.add_sub_of_le lower] using upper
    · simpa only [Nat.add_sub_of_le lower] using observed

private theorem prefix_of_interval
    (steps : ∀ i, begin ≤ i → i < finish → Step primitives (micro i) (micro (i + 1)))
    (atFinish : entryOf (micro finish) = some next) {job : Job m ports} {stack : Stack m ports final} {store : σ}
    (atBegin : micro begin = ⟨.eval job stack, store⟩) (before : begin < finish)
    (live : BeforeReturn (fun i => (micro i).control) begin finish stack)
    (earlier : EarlierCallsReturn (fun i => (micro i).control) begin finish) :
    ∃ pending, Prefix primitives job store next pending ∧ micro finish = next.config (pending.push stack) := by
  classical
  suffices search : ∀ distance start, finish - start = distance → start < finish →
      (∀ i, start ≤ i → i < finish → Step primitives (micro i) (micro (i + 1))) →
      ∀ {active : Ports (Ty V S)} (job : Job m active) (stack : Stack m active final) (store : σ),
        micro start = ⟨.eval job stack, store⟩ →
        BeforeReturn (fun i => (micro i).control) start finish stack →
        EarlierCallsReturn (fun i => (micro i).control) start finish →
        ∃ pending, Prefix primitives job store next pending ∧ micro finish = next.config (pending.push stack) from
    search _ begin rfl before steps job stack store atBegin live earlier
  intro distance
  induction distance using Nat.strong_induction_on with
  | ind distance ih =>
    intro start distanceEq before steps active job stack store actual lives completed
    have search {active' : Ports (Ty V S)} {cursor : Nat} {job' : Job m active'} {stack' : Stack m active' final}
        {store' : σ} (after : start < cursor) (bound : cursor < finish)
        (actual' : micro cursor = ⟨.eval job' stack', store'⟩)
        (live' : BeforeReturn (fun i => (micro i).control) cursor finish stack') :
        ∃ pending, Prefix primitives job' store' next pending ∧ micro finish = next.config (pending.push stack') :=
      ih (finish - cursor) (by omega) cursor rfl bound (fun i lower => steps i (by omega))
        job' stack' store' actual' live' (fun i lower => completed i (by omega))
    have firstEdge := steps start (Nat.le_refl _) before
    have firstReturn {p : Ports (Ty V S)} {job' : Job m p} {frame : Stack m p final}
        (entered : micro (start + 1) = ⟨.eval job' frame, store⟩) :=
      first_return (finish := finish) (fun i lower => steps i (by omega)) entered
    cases job with
    | call callee arguments =>
      obtain ⟨j, later, sooner, returned⟩ := completed start (Nat.le_refl _) before callee arguments stack
        (congrArg Config.control actual)
      exact False.elim (lives j (by omega) sooner returned)
    | iteration body input =>
      let frame := Stack.loop body stack
      let active := Job.region body input (PUnit.unit : Locals m.Val [])
      have entered : micro (start + 1) = ⟨.eval active frame, store⟩ :=
        advance actual firstEdge (.of_next_some rfl)
      rcases firstReturn entered with ⟨stop, afterEnter, inTime, value, returned, ran⟩ | under
      · cases value with
        | cons tag values =>
          have after := steps stop (by omega) inTime
          by_cases again : (tag.selector.val == 1) = true
          · have edge : Step primitives ⟨.returned (.cons tag values) frame, (micro stop).store⟩
                ⟨.eval (.iteration body values) stack, (micro stop).store⟩ := by
              apply Step.of_next_some
              change _root_.Part.some (Config.mk (State.finishLoop body tag values stack) (micro stop).store) = _
              rw [State.finishLoop, ite_eq_left again]
            have restarted := advance (at_control returned) after edge
            generalize (micro stop).store = middle at ran restarted
            have stillBefore := before_entry (by omega) restarted rfl atFinish
            obtain ⟨pending, loop, observed⟩ := search (by omega) stillBefore restarted
              (fun i lower upper => lives i (by omega) upper)
            have first : Feedback.Iteration primitives body (input, store) (values, middle) :=
              ⟨tag, ran, again⟩
            cases loop with
            | iteration completedFeedback inBody =>
              exact ⟨_, .iteration (completedFeedback.head first) inBody, observed⟩
          · have edge : Step primitives ⟨.returned (.cons tag values) frame, (micro stop).store⟩
                ⟨.returned values stack, (micro stop).store⟩ := by
              apply Step.of_next_some
              change _root_.Part.some (Config.mk (State.finishLoop body tag values stack) (micro stop).store) = _
              rw [State.finishLoop, ite_eq_right again]
            have exited := advance (at_control returned) after edge
            exact False.elim (lives _ (by omega) (before_entry (by omega) exited rfl atFinish)
              ⟨_, congrArg Config.control exited⟩)
      · have inTime := before_entry (by omega) entered rfl atFinish
        obtain ⟨pending, inBody, observed⟩ := search (by omega) inTime entered under
        exact ⟨.loop body pending, .iteration (input := (input, store)) (current := (input, store)) .refl inBody, observed⟩
    | region body entry locals =>
      cases body with
      | ret wires =>
        have reached : micro (start + 1) = ⟨.returned (wires.read entry locals) stack, store⟩ :=
          advance actual firstEdge (.of_next_some rfl)
        have within := before_entry (by omega) reached rfl atFinish
        exact False.elim (lives _ (by omega) within ⟨_, congrArg Config.control reached⟩)
      | bind node children rest =>
        let frame := Stack.resume rest entry locals stack
        let nodeJob := Job.node node.kind node.childSigs children (node.inputs.read entry locals)
        have entered : micro (start + 1) = ⟨.eval nodeJob frame, store⟩ :=
          advance actual firstEdge (.of_next_some rfl)
        have inTime := before_entry (by omega) entered rfl atFinish
        rcases firstReturn entered with ⟨stop, afterEnter, returnedBefore, value, returned, ran⟩ | under
        · have resumed : micro (stop + 1) =
              ⟨.eval (.region rest entry (locals.snoc value)) stack, (micro stop).store⟩ :=
            advance (at_control returned) (steps stop (by omega) returnedBefore) (.of_next_some rfl)
          have stillBefore := before_entry (by omega) resumed rfl atFinish
          obtain ⟨pending, later, observed⟩ := search (by omega) stillBefore resumed
            (fun i lower upper => lives i (by omega) upper)
          exact ⟨pending, .later ran later, observed⟩
        · obtain ⟨pending, inside, observed⟩ := search (by omega) inTime entered under
          exact ⟨.bind rest entry locals pending, .inside inside, observed⟩
    | node kind cs children input =>
      cases kind with
      | theta =>
        have entered : micro (start + 1) = ⟨.eval (.iteration (children (0 : Fin 1)) input) stack, store⟩ :=
          advance actual firstEdge (.of_next_some rfl)
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
              have entered : micro (start + 1) = ⟨.eval (.region (children tag) inputs PUnit.unit) stack, store⟩ :=
                advance actual firstEdge (.of_next_some rfl)
              have inTime := before_entry (by omega) entered rfl atFinish
              obtain ⟨pending, inArm, observed⟩ := search (by omega) inTime entered
                (fun i lower upper => lives i (by omega) upper)
              exact ⟨pending, .gamma inArm, observed⟩
        | simple instruction =>
          cases instruction with
          | primitive opcode =>
            rw [actual] at firstEdge
            change micro (start + 1) ∈ ((primitives.step opcode input).run store).map
              (fun (value, finalStore) => Config.mk (.returned value stack) finalStore) at firstEdge
            obtain ⟨⟨value, finalStore⟩, _, observed⟩ := (_root_.Part.mem_map_iff _).mp firstEdge
            have returned := observed.symm
            have within := before_entry (by omega) returned rfl atFinish
            exact False.elim (lives _ (by omega) within ⟨value, congrArg Config.control returned⟩)
          | apply fn =>
            cases input with
            | cons callee args =>
              let selected : Entry m σ := ⟨⟨fn.results, ⟨fn.args, callee, args⟩⟩, store⟩
              have entered : micro (start + 1) = selected.config stack :=
                advance actual firstEdge (.of_next_some rfl)
              have first : start + 1 = finish := by
                by_contra notFirst
                obtain ⟨i, later, sooner, returned⟩ :=
                  completed (start + 1) (by omega) (by omega) callee args stack (congrArg Config.control entered)
                exact lives i (by omega) sooner returned
              have observed : micro finish = selected.config stack := first ▸ entered
              have same : selected = next := Option.some.inj
                ((show entryOf (selected.config stack) = some selected from rfl).symm.trans
                  ((congrArg entryOf observed).symm.trans atFinish))
              subst next
              exact ⟨.empty, .apply callee args store, observed⟩

theorem entry_of_interval
    (steps : ∀ i, begin ≤ i → i < finish → Step primitives (micro i) (micro (i + 1)))
    {caller : Entry m σ} {stack : Stack m caller.call.results final} {nextStack : Stack m next.call.results final}
    (atCaller : micro begin = caller.config stack) (atCallee : micro finish = next.config nextStack)
    (rising : begin < finish)
    (live : BeforeReturn (fun i => (micro i).control) (begin + 1) finish stack)
    (earlier : EarlierCallsReturn (fun i => (micro i).control) (begin + 1) finish) :
    ∃ pending, Prefix primitives caller.call.openBody caller.store next pending ∧ pending.push stack = nextStack := by
  have opened : micro (begin + 1) = ⟨.eval caller.call.openBody stack, caller.store⟩ :=
    advance atCaller (steps begin (Nat.le_refl _) rising) (.of_next_some rfl)
  have selected : entryOf (micro finish) = some next := by
    rw [atCallee]
    cases next with
    | mk call store =>
      cases call with
      | mk results activation => cases activation; rfl
  have before := before_entry (Nat.succ_le_of_lt rising) opened rfl selected
  obtain ⟨pending, independent, observed⟩ :=
    prefix_of_interval (fun i lower => steps i (by omega)) selected opened before live earlier
  have same := observed.symm.trans atCallee
  exact ⟨pending, independent, by cases same; rfl⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Proofs
