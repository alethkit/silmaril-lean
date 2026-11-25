module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Tests

private abbrev T := Ty Unit Unit
private abbrev word : T := .value (.data ())
private abbrev state : T := .state ()
private abbrev tag : T := .control 2
private abbrev decision : Ports T := [tag, word]
private abbrev results : Ports T := [word, state]
private abbrev route : Ports T := [tag, word, state]
private abbrev fn : Function Unit Unit := ⟨[word, state], results⟩
private abbrev callable : T := fn.port
private abbrev bodyArgs : Ports T := callable :: fn.args

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | choose : Op [word] decision
  | prefix : Op [state] [state]
  | base : Op [state] results
  | suffix : Op [word, state, state] results
  | loopPrepare : Op [state] results
  | loopRoute : Op [word, state] route
  | loopAgain : Op [word, state] route

private def machine : Machine Op where
  Data _ := Nat
  State _ := List Nat
  primitive
    | .choose, .cons (.data n) .nil =>
      .cons (.control (if n = 0 then 0 else 1)) (.cons (.data (n - 1)) .nil)
    | .prefix, .cons (.state history) .nil => .cons (.state (history ++ [1])) .nil
    | .base, .cons (.state history) .nil =>
      .cons (.data (10 : Nat)) (.cons (.state (history ++ [2])) .nil)
    | .suffix, .cons (.data n) (.cons (.state returned) (.cons (.state saved) .nil)) =>
      .cons (.data (n + 1)) (.cons (.state (returned ++ [3, saved.length])) .nil)
    | .loopPrepare, .cons (.state history) .nil =>
      .cons (.data (0 : Nat)) (.cons (.state (history ++ [4])) .nil)
    | .loopRoute, .cons (.data n) (.cons (.state history) .nil) =>
      let again := 1 < n
      .cons (.control (if again then 1 else 0)) <|
        .cons (.data (n - 1)) <| .cons (.state (history ++ [if again then 5 else 6])) .nil
    | .loopAgain, .cons (.data n) (.cons (.state history) .nil) =>
      .cons (.control 1) (.cons (.data (n + 1)) (.cons (.state (history ++ [5])) .nil))

private def prefixNode : NestedTheta.Node (Instruction Op) bodyArgs [] [state] :=
  ⟨[state], .base (.simple (.primitive .prefix)), .cons (.arg (.tail (.tail .head))) .nil, fun i => i.elim0⟩

private def applyNode : NestedTheta.Node (Instruction Op) bodyArgs [[state]] results :=
  ⟨bodyArgs, .base (.simple (.apply fn)),
    .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) .head) .nil)), fun i => i.elim0⟩

private def suffixNode : NestedTheta.Node (Instruction Op) bodyArgs [[state], results] results :=
  ⟨[word, state, state], .base (.simple (.primitive .suffix)),
    .cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head))
      (.cons (.output (0 : Fin 2) .head) .nil)), fun i => i.elim0⟩

private def suffix : NestedTheta.Term (Instruction Op) bodyArgs [[state], results] [results] results :=
  .bind suffixNode (fun i => i.elim0)
    (.ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil)))

private def recurse : NestedTheta.Term (Instruction Op) bodyArgs [] [[state], results, results] results :=
  .bind prefixNode (fun i => i.elim0) (.bind applyNode (fun i => i.elim0) suffix)

private def baseNode : NestedTheta.Node (Instruction Op) bodyArgs [] results :=
  ⟨[state], .base (.simple (.primitive .base)), .cons (.arg (.tail (.tail .head))) .nil, fun i => i.elim0⟩

private def base : NestedTheta.Term (Instruction Op) bodyArgs [] [results] results :=
  .bind baseNode (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def chooseNode : NestedTheta.Node (Instruction Op) bodyArgs [] decision :=
  ⟨[word], .base (.simple (.primitive .choose)), .cons (.arg (.tail .head)) .nil, fun i => i.elim0⟩

private def gammaNode : NestedTheta.Node (Instruction Op) bodyArgs [decision] results :=
  ⟨tag :: bodyArgs, .base (.gamma 0),
    .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail .head))
      (.cons (.arg (.tail (.tail .head))) .nil))),
    Fin.cases [results] (fun _ => [[state], results, results])⟩

private def gammaRest : NestedTheta.Term (Instruction Op) bodyArgs [decision, results] [] results :=
  .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))

private def body : NestedTheta.Term (Instruction Op) bodyArgs [] [decision, results] results :=
  .bind chooseNode (fun i => i.elim0) (.bind gammaNode (Fin.cases base (fun _ => recurse)) gammaRest)

private def member : LambdaTerm Op [callable] [] fn :=
  ⟨[callable], .cons (.arg .head) .nil, [decision, results], body⟩

private def group : PhiTerm Op [] [] [fn] :=
  ⟨[], .nil, .cons member .nil⟩

private def linked : OmegaTerm Op [] [callable] [[callable]] :=
  ⟨.bind (.phi group) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def callee : machine.Val callable :=
  (Recursive.linkGraph machine 17 linked.toGraph .nil).get .head

private def arguments (n : Nat) (history : List Nat) : Tuple machine.Val fn.args :=
  .cons (.data n) (.cons (.state history) .nil)

private def initial : Job machine results :=
  .call callee (arguments 2 [])

private def waiting
    (rest : NestedTheta.Term (Instruction Op) bodyArgs [[state], results] [results] results)
    (n : Nat) (history : List Nat) (outer : Stack machine results results) :
    Stack machine results results :=
  let callerEntry := Tuple.cons callee (arguments n history)
  let callerLocals : Locals machine.Val [decision] :=
    (machine.primitive .choose (.cons (.data n) .nil), PUnit.unit)
  let selectedEntry := Tuple.cons callee (arguments (n - 1) history)
  let saved : Locals machine.Val [[state]] := (.cons (.state (history ++ [1])) .nil, PUnit.unit)
  .resume rest selectedEntry saved (.resume gammaRest callerEntry callerLocals outer)

/-- At the base call, each of the two recursive applications is waiting for
its actual returned tuple, with its own state snapshot and nonempty suffix. -/
example : State.runFor 22 (start initial) =
    .eval (.call callee (arguments 0 [1, 1])) (waiting suffix 1 [1] (waiting suffix 2 [] .halt)) := by
  let rest := suffix.toGraph.toTerm
  have reached : State.runFor 22 (start initial) =
      .eval (.call callee (arguments 0 [1, 1])) (waiting rest 1 [1] (waiting rest 2 [] .halt)) := by cbv
  simpa only [rest, NestedTheta.Term.toTerm_toGraph] using reached

private def expected : Tuple machine.Val results :=
  .cons (.data (12 : Nat)) (.cons (.state ([1, 1, 2, 3, 2, 3, 1] : List Nat)) .nil)

private theorem completes : Completes (start initial) expected :=
  completes_runFor (fuel := 64) (by cbv)

example : Admitted (start initial) := admitted_of_completes completes

example : Returns machine initial expected := completes_sound completes

example : invoke machine 0 3 callee (arguments 2 []) = some expected := by cbv

example : Completes (start initial) expected :=
  (completes_call_iff_invoke callee (arguments 2 []) (admitted_of_completes completes)).2
    ⟨0, 3, by cbv⟩

private def loopPrepareNode : NestedTheta.Node (Instruction Op) bodyArgs [] results :=
  ⟨[state], .base (.simple (.primitive .loopPrepare)),
    .cons (.arg (.tail (.tail .head))) .nil, fun i => i.elim0⟩

private def loopApplyNode : NestedTheta.Node (Instruction Op) bodyArgs [results] results :=
  ⟨bodyArgs, .base (.simple (.apply fn)),
    .cons (.arg .head) (.cons (.output (0 : Fin 1) .head)
      (.cons (.output (0 : Fin 1) (.tail .head)) .nil)), fun i => i.elim0⟩

private def loopRouteNode (opcode : Op [word, state] route) :
    NestedTheta.Node (Instruction Op) bodyArgs [results, results] route :=
  ⟨[word, state], .base (.simple (.primitive opcode)),
    .cons (.arg (.tail .head)) (.cons (.output (1 : Fin 2) (.tail .head)) .nil), fun i => i.elim0⟩

private def loopFinish (opcode : Op [word, state] route) :
    NestedTheta.Term (Instruction Op) bodyArgs [results, results] [route] (Theta.BodyResults bodyArgs) :=
  .bind (loopRouteNode opcode) (fun i => i.elim0) <|
    .ret (.cons (.output (2 : Fin 3) .head) (.cons (.arg .head)
      (.cons (.output (2 : Fin 3) (.tail .head)) (.cons (.output (2 : Fin 3) (.tail (.tail .head))) .nil))))

private def loopBody (opcode : Op [word, state] route) :
    NestedTheta.Term (Instruction Op) bodyArgs [] [results, results, route]
    (Theta.BodyResults bodyArgs) :=
  .bind loopPrepareNode (fun i => i.elim0) <|
    .bind loopApplyNode (fun i => i.elim0) (loopFinish opcode)

private def loopNode : NestedTheta.Node (Instruction Op) bodyArgs [[state]] bodyArgs :=
  ⟨bodyArgs, .theta bodyArgs,
    .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) .head) .nil)),
    fun _ => [results, results, route]⟩

private def postLoop : NestedTheta.Node (Instruction Op) bodyArgs [[state], bodyArgs] results :=
  ⟨[word, state, state], .base (.simple (.primitive .suffix)),
    .cons (.output (1 : Fin 2) (.tail .head)) (.cons (.output (1 : Fin 2) (.tail (.tail .head)))
      (.cons (.output (0 : Fin 2) .head) .nil)), fun i => i.elim0⟩

private def driverSuffix : NestedTheta.Term (Instruction Op) bodyArgs [[state], bodyArgs] [results] results :=
  .bind postLoop (fun i => i.elim0) <|
    .ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil))

private def driverBody (opcode : Op [word, state] route) :
    NestedTheta.Term (Instruction Op) bodyArgs [] [[state], bodyArgs, results] results :=
  .bind prefixNode (fun i => i.elim0) (.bind loopNode (fun _ => loopBody opcode) driverSuffix)

private def driver (opcode : Op [word, state] route) : LambdaTerm Op [] [[callable]] fn :=
  ⟨[callable], .cons (.output (0 : Fin 1) .head) .nil, [[state], bodyArgs, results], driverBody opcode⟩

private def loopModule (opcode : Op [word, state] route) : OmegaTerm Op [] [callable] [[callable], [callable]] :=
  ⟨.bind (.phi group) <| .bind (.lambda (driver opcode)) <| .ret (.cons (.output (1 : Fin 2) .head) .nil)⟩

private def linkedDriver (opcode : Op [word, state] route) : machine.Val callable :=
  (Recursive.linkGraph machine 19 (loopModule opcode).toGraph .nil).get .head

private def loopJob : Job machine results := .call (linkedDriver .loopRoute) (arguments 2 [])

private def waitingParent (n : Nat) : Stack machine bodyArgs results :=
  .resume (past := [[state]]) driverSuffix.toGraph.toTerm (.cons callee (arguments n []))
    (.cons (.state ([1] : List Nat)) .nil, PUnit.unit) .halt

-- The feedback step starts a second body with empty locals and retains
-- the original parent continuation.
example : State.runFor 31 (start loopJob) =
    .eval (.region (loopBody .loopRoute).toGraph.toTerm (.cons callee (arguments 1 [1, 4, 2, 5])) PUnit.unit)
      (.loop (loopBody .loopRoute).toGraph.toTerm (waitingParent 2)) := by cbv

-- Exit hands the carried tuple to the same parent, discarding the tag.
example : State.runFor 54 (start loopJob) =
    .returned (.cons callee (arguments 0 [1, 4, 2, 5, 4, 2, 6])) (waitingParent 2) := by cbv

private def loopExpected : Tuple machine.Val results :=
  .cons (.data (1 : Nat)) (.cons (.state ([1, 4, 2, 5, 4, 2, 6, 3, 1] : List Nat)) .nil)

-- The two visits each call the linked φ member (2). Only the first
-- feeds back (5). The exit (6) is followed by the parent's suffix (3, 1).
example : Completes (start loopJob) loopExpected :=
  completes_runFor (fuel := 128) (by cbv)

example : invoke machine 1 2 (linkedDriver .loopRoute) (arguments 2 []) = none := by cbv

private theorem linkedReturns : Returns machine loopJob loopExpected :=
  (Recursive.call_iff machine (linkedDriver .loopRoute) (arguments 2 []) loopExpected).2 ⟨2, 2, by cbv⟩

example : Completes (start loopJob) loopExpected :=
  completes_iff_returns.mpr linkedReturns

private def history : Nat → List Nat
  | 0 => [1]
  | n + 1 => ((history n ++ [4]) ++ [2]) ++ [5]

private def feedbackInputs (n : Nat) : Tuple machine.Val bodyArgs :=
  .cons callee (arguments n (history n))

private abbrev feedbackBody := (loopBody .loopAgain).toGraph.toTerm

private def feedbackJob : Job machine results := .call (linkedDriver .loopAgain) (arguments 0 [])

private theorem linkedBaseReturns (log : List Nat) :
    Returns machine (.call callee (arguments 0 log))
      (.cons (.data (10 : Nat)) (.cons (.state (log ++ [2])) .nil)) :=
  (Recursive.call_iff machine callee (arguments 0 log) _).2 ⟨0, 1, by cbv⟩

private theorem completedIteration (n : Nat) :
    Feedback.Iteration feedbackBody (feedbackInputs n) (feedbackInputs (n + 1)) := by
  refine ⟨.control 1, ?_, rfl⟩
  have ran : Returns machine
      (.region (loopBody .loopAgain) (feedbackInputs n) (PUnit.unit : Locals machine.Val []))
      (.cons (.control (1 : Fin 2)) (feedbackInputs (n + 1))) := by
    refine Returns.bind (node := loopPrepareNode) (.primitive Op.loopPrepare _ _ _) ?_
    refine Returns.bind (node := loopApplyNode) (.apply (linkedBaseReturns (history n ++ [4]))) ?_
    refine Returns.bind (node := loopRouteNode Op.loopAgain) (.primitive Op.loopAgain _ _ _) ?_
    exact .ret _ _ _
  exact Eq.mpr (congrArg (fun term =>
    Returns machine (.region (past := []) term (feedbackInputs n) (PUnit.unit : Locals machine.Val []))
      (.cons (.control (1 : Fin 2)) (feedbackInputs (n + 1))))
    (NestedTheta.Term.toTerm_toGraph (loopBody Op.loopAgain))) ran

-- Enter the actual linked driver's loop and check two concrete feedback edges.
private theorem reachedInitial :
    State.runFor 6 (start feedbackJob) = Feedback.restart feedbackBody (waitingParent 0) (feedbackInputs 0) := by cbv

example : State.runFor 30 (start feedbackJob) =
    Feedback.restart feedbackBody (waitingParent 0) (feedbackInputs 1) := by cbv

example : State.runFor 54 (start feedbackJob) =
    Feedback.restart feedbackBody (waitingParent 0) (feedbackInputs 2) := by cbv

private theorem linkedRestarts : ∃ micro indices,
    Feedback.RestartTrace feedbackBody (waitingParent 0) feedbackInputs micro indices :=
  (Feedback.iterations_iff_restarts feedbackInputs).mp completedIteration

example : Feedback.Run feedbackBody (feedbackInputs 0) := by
  obtain ⟨micro, indices, trace⟩ := linkedRestarts
  exact Feedback.run_iff_restarts.mpr ⟨feedbackInputs, micro, indices, rfl, trace⟩

example : InfiniteTrace Step (start feedbackJob) := by
  obtain ⟨micro, indices, trace⟩ := linkedRestarts
  have initial := trace.atRestart 0
  rw [trace.first] at initial
  exact InfiniteTrace.of_steps (reachedInitial ▸ runFor_reachable 6 (start feedbackJob))
    ⟨micro, initial, trace.steps⟩

open Feedback.Divergence in
example : ∃ micro extracted indices,
    extracted 0 = feedbackInputs 0 ∧ Feedback.RestartTrace feedbackBody (waitingParent 0) extracted micro indices := by
  obtain ⟨micro, indices, trace⟩ := linkedRestarts
  have initial := trace.atRestart 0
  rw [trace.first] at initial
  have stays := (stays_iff_decomposes trace.steps initial).mpr (.inl ⟨_, _, rfl, trace⟩)
  exact ⟨micro, ((stays_iff_decomposes trace.steps initial).mp stays).resolve_right
    (fun ⟨last, _, forever⟩ => no_bodyForever_of_restarts trace last forever)⟩

private def endlessMember : LambdaTerm Op [callable] [] fn :=
  ⟨[callable], .cons (.arg .head) .nil, [[state], results, results], recurse⟩

private def endlessGroup : PhiTerm Op [] [] [fn] :=
  ⟨[], .nil, .cons endlessMember .nil⟩

private def endlessModule : OmegaTerm Op [] [callable, callable] [[callable], [callable]] :=
  ⟨.bind (.phi endlessGroup) <| .bind (.lambda (driver .loopAgain)) <|
    .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))⟩

private def endlessExports : Tuple machine.Val [callable, callable] :=
  Recursive.linkGraph machine 23 endlessModule.toGraph .nil

private def endlessCallee : machine.Val callable := endlessExports.get .head

private def endlessJob : Job machine results := .call (endlessExports.get (.tail .head)) (arguments 0 [])

private def endlessParent : Stack machine bodyArgs results :=
  .resume (past := [[state]]) driverSuffix.toGraph.toTerm (.cons endlessCallee (arguments 0 []))
    (.cons (.state ([1] : List Nat)) .nil, PUnit.unit) .halt

private def endlessInput : Tuple machine.Val bodyArgs := .cons endlessCallee (arguments 0 [1])

private theorem endlessBodyReached : State.runFor 7 (start endlessJob) =
    .eval (.region feedbackBody endlessInput PUnit.unit) (.loop feedbackBody endlessParent) := by cbv

private def endlessWaiting (log : List Nat) (outer : Stack machine results results) :
    Stack machine results results :=
  .resume (past := [[state]]) suffix.toGraph.toTerm (.cons endlessCallee (arguments 0 log))
    (.cons (.state (log ++ [1])) .nil, PUnit.unit) outer

-- The second recursive activation still has two pending non-tail suffixes.
-- Its state includes the driver's prefix, the θ body's prepare, and both call prefixes.
example : State.runFor 24 (start endlessJob) =
    .eval (.call endlessCallee (arguments 0 [1, 4, 1, 1]))
      (endlessWaiting [1, 4, 1] (endlessWaiting [1, 4]
        (.resume (past := [results]) (loopFinish .loopAgain).toGraph.toTerm
          endlessInput (arguments 0 [1, 4], PUnit.unit) (.loop feedbackBody endlessParent)))) := by cbv

private theorem endlessInvoke (loops depth n : Nat) (log : List Nat) :
    invoke machine loops depth endlessCallee (arguments n log) = none := by
  induction depth generalizing log with
  | zero => rfl
  | succ depth ih =>
    let entry := Tuple.cons endlessCallee (arguments n log)
    let saved : Locals machine.Val [[state]] := (.cons (.state (log ++ [1])) .nil, PUnit.unit)
    change (invoke machine loops depth endlessCallee (arguments n (log ++ [1])) >>= fun output =>
      evalBody machine (dispatch machine (invoke machine loops depth)) loops
        suffix.toGraph.toTerm entry (saved.snoc output)) = none
    rw [ih]
    rfl

private theorem endlessNoReturn (values : Tuple machine.Val (Theta.BodyResults bodyArgs)) :
    ¬ Returns machine (.region feedbackBody endlessInput (PUnit.unit : Locals machine.Val [])) values := by
  intro returned
  obtain ⟨depth, loops, eventually⟩ := Recursive.returns_eventually machine returned
  have ran := eventually loops depth (Nat.le_refl _) (Nat.le_refl _)
  let locals : Locals machine.Val [results] := (arguments 0 [1, 4], PUnit.unit)
  change (invoke machine loops depth endlessCallee (arguments 0 [1, 4]) >>= fun output =>
    evalBody machine (dispatch machine (invoke machine loops depth)) loops
      (loopFinish .loopAgain).toGraph.toTerm endlessInput
      (locals.snoc output)) = some values at ran
  rw [endlessInvoke] at ran
  cases ran

private theorem endlessBodyInfinite :
    InfiniteTrace (Feedback.InsideStep (.loop feedbackBody endlessParent))
      (.eval (.region feedbackBody endlessInput PUnit.unit) (.loop feedbackBody endlessParent)) :=
  Feedback.trace_without_return (.loop feedbackBody endlessParent) _ endlessNoReturn

open Feedback.Divergence in
example : ∃ micro : Nat → State machine results,
    micro 0 = State.runFor 7 (start endlessJob) ∧
    (∀ i, Feedback.InsideStep (.loop feedbackBody endlessParent) (micro i) (micro (i + 1))) ∧
    (∃ last, Relation.ReflTransGen
      (Interval feedbackBody endlessParent (withEntry feedbackBody endlessParent endlessInput micro))
      (0, endlessInput) last ∧
      BodyForever feedbackBody endlessParent (withEntry feedbackBody endlessParent endlessInput micro) last) := by
  obtain ⟨micro, initial, inside⟩ := endlessBodyInfinite
  have stays : StaysInLoop feedbackBody endlessParent micro := fun i _ _ returned =>
    False.elim ((inside i).2 ⟨_, returned⟩)
  have zeroIterations : BodyForever feedbackBody endlessParent
      (withEntry feedbackBody endlessParent endlessInput micro) (0, endlessInput) := by
    refine ⟨rfl, ?_⟩
    intro i later
    cases i with
    | zero => cases later
    | succ i => exact (inside i).2
  exact ⟨micro, initial.trans endlessBodyReached.symm, inside,
    (body_decomposes (fun i => (inside i).1) initial stays).resolve_left
      (fun ⟨_, _, _, trace⟩ => no_bodyForever_of_restarts trace (0, endlessInput) zeroIterations)⟩

example : InfiniteTrace Step (start endlessJob) := by
  obtain ⟨micro, initial, steps, _⟩ :=
    Feedback.Divergence.trace_of_iterations_then_body .refl endlessBodyInfinite
  have reached : State.runFor 6 (start endlessJob) =
      Feedback.restart feedbackBody endlessParent endlessInput := by cbv
  exact InfiniteTrace.of_steps (reached ▸ runFor_reachable 6 (start endlessJob)) ⟨micro, initial, steps⟩

private def endlessEntry (log : List Nat) : Descent.Entry machine :=
  ⟨results, ⟨fn.args, endlessCallee, arguments 0 log⟩⟩

private theorem endlessCallNoReturn (log : List Nat) (output : Tuple machine.Val results) :
    ¬ Returns machine (endlessEntry log).activation.job output := by
  intro returned
  obtain ⟨loops, depth, evaluated⟩ := (Recursive.call_iff machine endlessCallee (arguments 0 log) output).mp returned
  rw [endlessInvoke] at evaluated
  cases evaluated

private theorem runFor_slice {micro : Nat → State machine results}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (i count : Nat) :
    State.runFor count (micro i) = micro (i + count) := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    rw [State.runFor, show (micro i).next = some (micro (i + 1)) from steps i]
    rw [show i + (count + 1) = i + 1 + count by omega]
    exact ih (i + 1)

-- Start at the real φ export with only a live microstep stream.
-- The concrete check at step 6 rules out the feedback alternative in this
-- example. No entry index, stack, or prefix is supplied to the splitter.
open Descent.Completeness in
example : ∃ micro : Nat → State machine results,
    micro 0 = (endlessEntry []).state .halt ∧
    (∀ i, Step (micro i) (micro (i + 1))) ∧
    HasFirstChild (endlessEntry []) .halt micro 0 := by
  obtain ⟨micro, initial, inside⟩ :=
    Feedback.trace_without_return .halt (endlessEntry []).activation.job (endlessCallNoReturn [])
  have steps (i : Nat) : Step (micro i) (micro (i + 1)) := (inside i).1
  have split := split_start steps initial
  refine ⟨micro, initial, steps, split.resolve_right ?_⟩
  intro feedback
  have reaches : State.runFor 6 ((endlessEntry []).state (.halt : Stack machine results results)) =
      (endlessEntry [1]).state (endlessWaiting [] .halt) := by cbv
  have observed : micro 6 = (endlessEntry [1]).state (endlessWaiting [] .halt) :=
    ((runFor_slice steps 0 6).symm.trans (congrArg (State.runFor 6) initial)).trans reaches
  exact feedback.1 6 (by decide) ⟨endlessEntry [1], endlessWaiting [] .halt, observed,
    live_of_no_return steps observed (endlessCallNoReturn [1])⟩

private abbrev controlPorts : Ports T := [tag]
private abbrev quietFn : Function Unit Unit := ⟨controlPorts, controlPorts⟩

private def quietBody :
    NestedTheta.Term (Instruction Op) controlPorts [] [] (Theta.BodyResults controlPorts) :=
  .ret (.cons (.arg .head) (.cons (.arg .head) .nil))

private def quietSuffix : NestedTheta.Term (Instruction Op) controlPorts [controlPorts] [] controlPorts :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def quietTerm : NestedTheta.Term (Instruction Op) controlPorts [] [controlPorts] controlPorts :=
  .bind (NestedTheta.thetaVertex []) (fun _ => quietBody) quietSuffix

private def quietGroup : PhiTerm Op [] [] [quietFn] :=
  ⟨[], .nil, .cons ⟨[], .nil, [controlPorts], quietTerm⟩ .nil⟩

private def quietModule : OmegaTerm Op [] [quietFn.port] [[quietFn.port]] :=
  ⟨.bind (.phi quietGroup) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def keepGoing : Tuple machine.Val controlPorts := .cons (.control 1) .nil

private def quietEntry : Descent.Entry machine :=
  ⟨controlPorts, ⟨controlPorts, (Recursive.linkGraph machine 29 quietModule.toGraph .nil).get .head, keepGoing⟩⟩

private def quietParent : Stack machine controlPorts controlPorts :=
  .resume (past := []) quietSuffix.toGraph.toTerm keepGoing PUnit.unit .halt

private abbrev decodedQuiet := quietBody.toGraph.toTerm

private def quietCycle (parent : Stack machine controlPorts controlPorts) (i : Nat) : State machine controlPorts :=
  match i % 3 with
  | 0 => Feedback.restart decodedQuiet parent keepGoing
  | 1 => .eval (.region decodedQuiet keepGoing PUnit.unit) (.loop decodedQuiet parent)
  | _ => .returned (.cons (.control 1) keepGoing) (.loop decodedQuiet parent)

private theorem quietCycleStep (parent : Stack machine controlPorts controlPorts) (i : Nat) :
    Step (quietCycle parent i) (quietCycle parent (i + 1)) := by
  have bound := Nat.mod_lt i (by decide : 0 < 3)
  have casesMod : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases casesMod with reduced | reduced | reduced <;>
    simp only [quietCycle, Nat.add_mod i 1 3, reduced] <;> rfl

private def quietMicro : Nat → State machine controlPorts
  | 0 => quietEntry.state .halt
  | 1 => .eval quietEntry.openBody .halt
  | 2 => State.runFor 2 (quietEntry.state .halt)
  | i + 3 => quietCycle quietParent i

private theorem quietSteps (i : Nat) : Step (quietMicro i) (quietMicro (i + 1)) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => cbv
  | j + 3 => exact quietCycleStep quietParent j

private theorem quietCycleNoCall (parent : Stack machine controlPorts controlPorts) (i : Nat) :
    Descent.Entry.ofState (quietCycle parent i) = none := by
  unfold quietCycle
  split <;> rfl

private theorem quietNoCall (i : Nat) (after : 0 < i) : Descent.Entry.ofState (quietMicro i) = none := by
  match i with
  | 0 => cases after
  | 1 => rfl
  | 2 => rfl
  | j + 3 => exact quietCycleNoCall quietParent j

-- The trace has an endless θ cycle but no deeper call. Its restart
-- indices are computed by the theorem without a checkpoint premise.
open Descent.Completeness in
example : HasFeedback quietMicro 1 := by
  have classified := split_start (caller := quietEntry) (micro := quietMicro) quietSteps rfl
  rcases classified with first | feedback
  · obtain ⟨i, child, pending, observed⟩ := first
    have noCall := quietNoCall i observed.later
    rw [observed.atEntry] at noCall
    cases child with
    | mk _ activation => cases activation; cases noCall
  · exact feedback.2

open Descent.Completeness.Global

private abbrev relayPorts : Ports T := quietFn.port :: controlPorts

private def relayApply : NestedTheta.Node (Instruction Op) relayPorts [] controlPorts :=
  ⟨relayPorts, .base (.simple (.apply quietFn)),
    (NestedTheta.identityPorts relayPorts).map (fun _ => .arg), fun i => i.elim0⟩

private def relaySuffix : NestedTheta.Term (Instruction Op) relayPorts [controlPorts] [] controlPorts :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def relayTerm : NestedTheta.Term (Instruction Op) relayPorts [] [controlPorts] controlPorts :=
  .bind relayApply (fun i => i.elim0) relaySuffix

private def relayLambda : LambdaTerm Op [] [[quietFn.port]] quietFn :=
  ⟨[quietFn.port], .cons (.output (0 : Fin 1) .head) .nil, [controlPorts], relayTerm⟩

private def relayModule : OmegaTerm Op [] [quietFn.port] [[quietFn.port], [quietFn.port]] :=
  ⟨.bind (.phi quietGroup) (.bind (.lambda relayLambda) (.ret (.cons (.output (1 : Fin 2) .head) .nil)))⟩

private def relayEntry : Descent.Entry machine :=
  linkedEntry machine 29 relayModule.toGraph .nil .head keepGoing

private def relayFrame : Stack machine controlPorts controlPorts :=
  .resume (past := []) relaySuffix.toGraph.toTerm
    (.cons quietEntry.activation.callee keepGoing) PUnit.unit .halt

private def relayThetaFrame : Stack machine controlPorts controlPorts :=
  .resume (past := []) quietSuffix.toGraph.toTerm keepGoing PUnit.unit relayFrame

private def relayMicro : Nat → State machine controlPorts
  | i + 6 => quietCycle relayThetaFrame i
  | i => State.runFor i (relayEntry.state .halt)

private theorem relaySteps (i : Nat) : Step (relayMicro i) (relayMicro (i + 1)) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => cbv
  | j + 6 => exact quietCycleStep relayThetaFrame j

private theorem relayNoCall (i : Nat) (after : 0 < i) (different : i ≠ 3) :
    Descent.Entry.ofState (relayMicro i) = none := by
  match i with
  | 0 => cases after
  | 1 => rfl
  | 2 => rfl
  | 3 => exact False.elim (different rfl)
  | 4 => rfl
  | 5 => rfl
  | j + 6 => exact quietCycleNoCall relayThetaFrame j

private def observedDepth : State machine controlPorts → Nat
  | .eval _ stack | .returned _ stack => Descent.stackDepth stack

private theorem relayChildLive : Descent.Completeness.LiveFrom relayMicro 3 relayFrame := by
  rintro i after ⟨output, returned⟩
  match i with
  | 0 | 1 | 2 => omega
  | 3 | 4 | 5 =>
    cbv at returned
    cases returned
  | j + 6 =>
    change quietCycle relayThetaFrame j = .returned output relayFrame at returned
    unfold quietCycle at returned
    split at returned
    · cases returned
    · cases returned
    · have clash : (3 : Nat) = 1 := congrArg observedDepth returned
      cases clash

private theorem relayCallIndex {point : Point machine controlPorts}
    (after : 0 < point.index) (observed : point.Live relayMicro) : point.index = 3 := by
  by_contra elsewhere
  have noCall := relayNoCall point.index after elsewhere
  rw [observed.1] at noCall
  cases point with
  | mk _ entry _ =>
    cases entry with
    | mk _ activation => cases activation; cases noCall

-- The raw execution starts at an ω export. One independently specified
-- call prefix leads into a φ member that runs a productive θ cycle.
private theorem relayObserved :
    ∃ last, Relation.TransGen (ChildStep relayMicro) (Point.root relayEntry) last ∧
      last.index = 3 ∧ last.Live relayMicro ∧
      (∀ i, last.index < i → ¬ Descent.Completeness.NonreturningCallAt relayMicro i) ∧
      Descent.Completeness.HasFeedback relayMicro (last.index + 1) := by
  have root : relayMicro 0 =
      start (.call ((Recursive.linkGraph machine 29 relayModule.toGraph .nil).get .head) keepGoing) := rfl
  have classified := classify_linked machine 29 relayModule.toGraph .nil .head keepGoing relaySteps root
  rcases classified with chain | ⟨last, path, live, closed, feedback⟩
  · obtain ⟨points, first, edges⟩ := chain
    have grows := (edges 0).grows.1
    rw [first] at grows
    have one : (points 1).index = 3 := relayCallIndex grows (edges 0).live
    have later : (points 1).index < (points 2).index := (edges 1).grows.1
    have two : (points 2).index = 3 := relayCallIndex (grows.trans later) (edges 1).live
    rw [one, two] at later
    exact False.elim ((Nat.lt_irrefl 3) later)
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with same | nonempty
    · subst last
      have child : relayMicro 3 = quietEntry.state relayFrame := by cbv
      exact False.elim (closed 3 (by decide) ⟨quietEntry, relayFrame, child, relayChildLive⟩)
    · exact ⟨last, nonempty, relayCallIndex (path_grows nonempty).1 live, live, closed, feedback⟩

private def relayInputs : Tuple machine.Val relayPorts :=
  .cons quietEntry.activation.callee keepGoing

private def relayPending : Descent.Pending machine controlPorts controlPorts :=
  .bind (past := []) relaySuffix relayInputs PUnit.unit .empty

private theorem relayToPhi : Descent.Prefix machine relayEntry.openBody quietEntry relayPending := by
  have openBody : relayEntry.openBody = .region relayTerm relayInputs PUnit.unit :=
    congrArg (fun term => Job.region (m := machine) (past := []) term relayInputs PUnit.unit)
      (NestedTheta.Term.toTerm_toGraph relayTerm)
  rw [openBody]
  exact .inside (node := relayApply) (.apply (fn := quietFn) quietEntry.activation.callee keepGoing)

private theorem quietFeedback : Feedback.Iteration quietBody keepGoing keepGoing :=
  ⟨.control 1, .ret _ _ _, rfl⟩

private def quietRestart : Descent.ThetaReach.Restart machine :=
  ⟨controlPorts, [], quietBody, keepGoing⟩

private def quietPending : Descent.Pending machine controlPorts controlPorts :=
  .bind (past := []) quietSuffix keepGoing PUnit.unit .empty

private theorem quietReaches : Descent.ThetaReach.Reaches machine quietEntry.openBody quietRestart quietPending := by
  have openBody : quietEntry.openBody = .region quietTerm keepGoing PUnit.unit :=
    congrArg (fun term => Job.region (m := machine) (past := []) term keepGoing PUnit.unit)
      (NestedTheta.Term.toTerm_toGraph quietTerm)
  rw [openBody]
  exact .inside (node := NestedTheta.thetaVertex []) (.theta (.restart (.single quietFeedback)))

-- A complete certificate from syntax, finite Returns, and productive
-- feedback. The finite route chooses the second restart of the θ body.
private theorem relayCertificate : Descent.ThetaReach.FeedbackRoute machine relayEntry .halt :=
  .call relayToPhi (.restart quietReaches ⟨fun _ => keepGoing, rfl, fun _ => quietFeedback⟩)

open Descent.ThetaReach in
example : InfiniteTrace Step (start (.call ((Recursive.linkGraph machine 29 relayModule.toGraph .nil).get .head)
    keepGoing)) :=
  (linked_iff machine 29 relayModule.toGraph .nil .head keepGoing).mp (.inr relayCertificate)

open Descent.ThetaReach in
example : FeedbackRoute machine relayEntry .halt := by
  obtain ⟨last, path, _, live, closed, feedback⟩ := relayObserved
  exact feedback_of_observation relaySteps ⟨last, path.to_reflTransGen, live, closed, feedback⟩

open Descent.ThetaReach in
example : Reaches machine (.iteration feedbackBody (feedbackInputs 0))
    ⟨bodyArgs, [results, results, route], feedbackBody, .cons callee (arguments 1 [1, 4, 2, 5])⟩ .empty :=
  .restart (.single (completedIteration 0))

open Descent.ThetaReach in
example : Diverges relayEntry :=
  (linked_iff machine 29 relayModule.toGraph .nil .head keepGoing).mpr ⟨relayMicro, rfl, relaySteps⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Tests
