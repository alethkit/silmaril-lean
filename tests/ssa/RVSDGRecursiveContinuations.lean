module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
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

private def loopRouteNode : NestedTheta.Node (Instruction Op) bodyArgs [results, results] route :=
  ⟨[word, state], .base (.simple (.primitive .loopRoute)),
    .cons (.arg (.tail .head)) (.cons (.output (1 : Fin 2) (.tail .head)) .nil), fun i => i.elim0⟩

private def loopBody : NestedTheta.Term (Instruction Op) bodyArgs [] [results, results, route]
    (Theta.BodyResults bodyArgs) :=
  .bind loopPrepareNode (fun i => i.elim0) <| .bind loopApplyNode (fun i => i.elim0) <|
    .bind loopRouteNode (fun i => i.elim0) <|
      .ret (.cons (.output (2 : Fin 3) .head) (.cons (.arg .head)
        (.cons (.output (2 : Fin 3) (.tail .head)) (.cons (.output (2 : Fin 3) (.tail (.tail .head))) .nil))))

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

private def driverBody : NestedTheta.Term (Instruction Op) bodyArgs [] [[state], bodyArgs, results] results :=
  .bind prefixNode (fun i => i.elim0) (.bind loopNode (fun _ => loopBody) driverSuffix)

private def driver : LambdaTerm Op [] [[callable]] fn :=
  ⟨[callable], .cons (.output (0 : Fin 1) .head) .nil, [[state], bodyArgs, results], driverBody⟩

private def loopModule : OmegaTerm Op [] [callable] [[callable], [callable]] :=
  ⟨.bind (.phi group) <| .bind (.lambda driver) <| .ret (.cons (.output (1 : Fin 2) .head) .nil)⟩

private def linkedDriver : machine.Val callable :=
  (Recursive.linkGraph machine 19 loopModule.toGraph .nil).get .head

private def loopJob : Job machine results := .call linkedDriver (arguments 2 [])

private def waitingParent : Stack machine bodyArgs results :=
  .resume (past := [[state]]) driverSuffix.toGraph.toTerm (.cons callee (arguments 2 []))
    (.cons (.state ([1] : List Nat)) .nil, PUnit.unit) .halt

-- The feedback step starts a second body with empty locals and retains
-- the original parent continuation.
example : State.runFor 31 (start loopJob) =
    .eval (.region loopBody.toGraph.toTerm (.cons callee (arguments 1 [1, 4, 2, 5])) PUnit.unit)
      (.loop loopBody.toGraph.toTerm waitingParent) := by cbv

-- Exit hands the carried tuple to the same parent, discarding the tag.
example : State.runFor 54 (start loopJob) =
    .returned (.cons callee (arguments 0 [1, 4, 2, 5, 4, 2, 6])) waitingParent := by cbv

private def loopExpected : Tuple machine.Val results :=
  .cons (.data (1 : Nat)) (.cons (.state ([1, 4, 2, 5, 4, 2, 6, 3, 1] : List Nat)) .nil)

-- The two visits each call the linked φ member (2). Only the first
-- feeds back (5). The exit (6) is followed by the parent's suffix (3, 1).
example : Completes (start loopJob) loopExpected :=
  completes_runFor (fuel := 128) (by cbv)

example : invoke machine 1 2 linkedDriver (arguments 2 []) = none := by cbv

private theorem linkedReturns : Returns machine loopJob loopExpected :=
  (Recursive.call_iff machine linkedDriver (arguments 2 []) loopExpected).2 ⟨2, 2, by cbv⟩

example : Completes (start loopJob) loopExpected :=
  completes_iff_returns.mpr linkedReturns

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Tests
