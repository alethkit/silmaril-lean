module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Thms
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

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Tests
