module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Tests

open Relation (ReflTransGen)

private abbrev T := Ty Unit Unit
private abbrev st : T := .state ()
private abbrev tag : T := .control 2
private abbrev answer : Ports T := [st]
private abbrev fn : Function Unit Unit := ⟨[tag, st], answer⟩
private abbrev callable : T := fn.port
private abbrev carried : Ports T := callable :: fn.args

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | tick : Op answer answer
  | undefined : Op answer answer

private def machine : Machine Op where
  Data _ := Nat
  State _ := Nat
  primitive
    | .tick, .cons (.state n) .nil => .cons (.state (n + 1)) .nil
    | .undefined, input => input

private def primitives : Primitives machine Nat where
  step
    | .tick, input => fun store => .some (machine.primitive .tick input, store + 1)
    | .undefined, _ => fun _ => _root_.Part.none

private def stateValue (n : Nat) : Tuple machine.Val answer := .cons (.state n) .nil

private def args (selector : Fin 2) (n : Nat) : Tuple machine.Val fn.args :=
  .cons (.control selector) (stateValue n)

private def undefinedNode : NestedTheta.Node (Instruction Op) answer [] answer :=
  ⟨answer, .base (.simple (.primitive .undefined)), .cons (.arg .head) .nil, fun i => i.elim0⟩

private def afterUndefined : NestedTheta.Term (Instruction Op) answer [answer] [] answer :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def gammaNode : NestedTheta.Node (Instruction Op) fn.args [] answer :=
  ⟨fn.args, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    Fin.cases [] (fun _ => [answer])⟩

private def afterGamma : NestedTheta.Term (Instruction Op) fn.args [answer] [] answer :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def memberBody : NestedTheta.Term (Instruction Op) fn.args [] [answer] answer :=
  .bind gammaNode (Fin.cases (.ret (.cons (.arg .head) .nil))
    (fun _ => .bind undefinedNode (fun i => i.elim0) afterUndefined)) afterGamma

private def group : PhiTerm Op [] [] [fn] :=
  ⟨[], .nil, .cons ⟨[], .nil, [answer], memberBody⟩ .nil⟩

private def tickNode : NestedTheta.Node (Instruction Op) carried [] answer :=
  ⟨answer, .base (.simple (.primitive .tick)), .cons (.arg (.tail (.tail .head))) .nil, fun i => i.elim0⟩

private def callNode : NestedTheta.Node (Instruction Op) carried [answer] answer :=
  ⟨carried, .base (.simple (.apply fn)),
    .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) .head) .nil)), fun i => i.elim0⟩

private def afterCall : NestedTheta.Term (Instruction Op) carried [answer, answer] [] (Theta.BodyResults carried) :=
  .ret (.cons (.arg (.tail .head)) (.cons (.arg .head) (.cons (.arg (.tail .head))
    (.cons (.output (1 : Fin 2) .head) .nil))))

private def loopBody : NestedTheta.Term (Instruction Op) carried [] [answer, answer] (Theta.BodyResults carried) :=
  .bind tickNode (fun i => i.elim0) (.bind callNode (fun i => i.elim0) afterCall)

private def loopNode : NestedTheta.Node (Instruction Op) carried [] carried :=
  NestedTheta.thetaVertex [answer, answer]

private def afterLoop : NestedTheta.Term (Instruction Op) carried [carried] [] answer :=
  .ret (.cons (.output (0 : Fin 1) (.tail (.tail .head))) .nil)

private def driverBody : NestedTheta.Term (Instruction Op) carried [] [carried] answer :=
  .bind loopNode (fun _ => loopBody) afterLoop

private def driverTerm : LambdaTerm Op [] [[callable]] fn :=
  ⟨[callable], .cons (.output (0 : Fin 1) .head) .nil, [carried], driverBody⟩

private def linked : OmegaTerm Op [] [callable, callable] [[callable], [callable]] :=
  ⟨.bind (.phi group) <| .bind (.lambda driverTerm) <|
    .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))⟩

private def exports : Tuple machine.Val [callable, callable] :=
  Recursive.linkGraph machine 47 linked.toGraph .nil

private def callee : machine.Val callable := exports.get .head
private def driver : machine.Val callable := exports.get (.tail .head)

private def carriedValues (selector : Fin 2) (n : Nat) : Tuple machine.Val carried :=
  .cons callee (args selector n)

private def entry (selector : Fin 2) : Job machine answer := .call driver (args selector 7)

private theorem openedMember (selector : Fin 2) (n : Nat) :
    Job.openClosure machine callee (args selector n) = .region memberBody (args selector n) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (args selector n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph memberBody)

private theorem openedDriver (selector : Fin 2) :
    Job.openClosure machine driver (args selector 7) = .region driverBody (carriedValues selector 7) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (carriedValues selector 7) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph driverBody)

private def tickSite : Site machine :=
  ⟨answer, answer, .tick, tickNode.childSigs, fun i => i.elim0, stateValue 7⟩

private def undefinedSite (n : Nat) : Site machine :=
  ⟨answer, answer, .undefined, undefinedNode.childSigs, fun i => i.elim0, stateValue n⟩

private theorem returnMember :
    Eval primitives (.call callee (args 0 8)) 21 (.returned (stateValue 8) 21) := by
  refine .call ?_
  rw [openedMember]
  exact .bind (node := gammaNode) (.gamma (tag := (0 : Fin 2)) (.ret _ _ _ _)) (.ret _ _ _ _)

private theorem returnRoot : Eval primitives (entry 0) 20 (.returned (stateValue 8) 21) := by
  refine .call ?_
  rw [openedDriver]
  refine Eval.bind (node := loopNode) (value := carriedValues 0 8) (middle := 21)
    (.theta (.stop (tag := .control 0) ?_ rfl)) ?_
  · refine Eval.bind (node := tickNode) (.primitive tickSite (_root_.Part.mem_some _)) ?_
    exact .bind (node := callNode) (.apply (fn := fn) returnMember) (.ret _ _ _ _)
  · exact .ret _ _ _ _

private def memberFrames : Descent.Pending machine answer answer :=
  .bind (past := []) afterGamma (args 1 8) PUnit.unit <|
    .bind (past := []) afterUndefined (stateValue 8) PUnit.unit .empty

private theorem blockMember :
    Eval primitives (.call callee (args 1 8)) 21 (.blocked (undefinedSite 8) memberFrames 21) := by
  refine .call ?_
  rw [openedMember]
  exact .bindBlocked (node := gammaNode) (.gamma (tag := (1 : Fin 2))
    (.bindBlocked (node := undefinedNode) (.primitiveBlocked (undefinedSite 8) 21 rfl)))

private def savedFrames : Descent.Pending machine answer answer :=
  .bind (past := []) afterLoop (carriedValues 1 7) PUnit.unit <| .loop loopBody <|
    .bind (past := [answer]) afterCall (carriedValues 1 7) (stateValue 8, PUnit.unit) memberFrames

private theorem blockRoot : Eval primitives (entry 1) 20 (.blocked (undefinedSite 8) savedFrames 21) := by
  refine .call ?_
  rw [openedDriver]
  refine Eval.bindBlocked (node := loopNode) (.theta (.loopBlocked ?_))
  refine Eval.bind (node := tickNode) (.primitive tickSite (_root_.Part.mem_some _)) ?_
  exact .bindBlocked (node := callNode) (.apply (fn := fn) blockMember)

-- The failing arm is undefined at the reached input and store, but tag 0
-- selects the other arm. Tick updates both the explicit wire and the store.
example : (primitives.step .undefined (stateValue 8)).run 21 = _root_.Part.none := rfl

example : ∃ reached : Config machine Nat answer,
    ReflTransGen (Step primitives) ⟨start (entry 0), 20⟩ reached ∧
      reached.result = some (stateValue 8, 21) :=
  ⟨_, returnRoot.steps .halt, rfl⟩

private def stopped : Config machine Nat answer :=
  ⟨.eval (undefinedSite 8).job (savedFrames.push .halt), 21⟩

-- With tag 1 the exact blocked configuration retains the outer θ,
-- the pending call and γ bindings, and the primitive's own continuation.
example : Descent.stackDepth (savedFrames.push (.halt : Stack machine answer answer)) = 5 := rfl

example : ReflTransGen (Step primitives) ⟨start (entry 1), 20⟩ stopped ∧
    stopped.Blocked primitives ∧ stopped.result = none ∧
    (∀ target, ¬ Step primitives stopped target) ∧
      ¬ InfiniteTrace (Step primitives) ⟨start (entry 1), 20⟩ := by
  have blocked := blockRoot.blocks (Stack.halt : Stack machine answer answer)
  have path := blockRoot.steps (Stack.halt : Stack machine answer answer)
  exact ⟨path, blocked, blocked.result_none, fun _ => blocked.no_step, no_infinite_of_reaches_blocked path blocked⟩

-- Take concrete machine steps without using either Eval derivation above.
private theorem stepThen {source next target : Config machine Nat answer}
    (picked : source.next primitives = _root_.Part.some next)
    (later : ReflTransGen (Step primitives) next target) : ReflTransGen (Step primitives) source target := by
  apply later.head
  change next ∈ source.next primitives
  rw [picked]
  exact _root_.Part.mem_some _

private theorem callThen {callee : machine.Val callable} {arguments : Tuple machine.Val fn.args}
    {body : Job machine answer} {stack : Stack machine answer answer}
    {store : Nat} {target : Config machine Nat answer}
    (opened : Job.openClosure machine callee arguments = body)
    (later : ReflTransGen (Step primitives) ⟨.eval body stack, store⟩ target) :
    ReflTransGen (Step primitives) ⟨.eval (.call callee arguments) stack, store⟩ target := by
  subst body
  exact stepThen rfl later

example : Eval primitives (entry 0) 20 (.returned (stateValue 8) 21) := by
  apply returns_iff_path.mpr
  refine callThen (openedDriver 0) ?_
  iterate 8 refine stepThen rfl ?_
  refine callThen (openedMember 0 8) ?_
  iterate 10 refine stepThen rfl ?_
  exact .refl

example : ∃ site pending, Eval primitives (entry 1) 20 (.blocked site pending 21) ∧
    stopped.control = .eval site.job (pending.push .halt) := by
  apply (blocked_iff_path (target := stopped)).mpr
  constructor
  · refine callThen (openedDriver 1) ?_
    iterate 8 refine stepThen rfl ?_
    refine callThen (openedMember 1 8) ?_
    iterate 3 refine stepThen rfl ?_
    exact .refl
  · exact ⟨⟨undefinedSite 8, savedFrames.push .halt⟩, rfl, rfl⟩

example : Eval (Primitives.liftTotal machine Nat) (entry 0) 20 (.returned (stateValue 8) 20) := by
  have returned : Recursive.Returns machine (entry 0) (stateValue 8) :=
    (Recursive.call_iff machine driver (args 0 7) (stateValue 8)).2 ⟨1, 2, by cbv⟩
  exact eval_liftTotal_iff.mpr ⟨returned, rfl⟩

private def feedbackPrimitives (limit : Option Nat) : Primitives machine Nat where
  step
    | .tick, input => fun store => .some (machine.primitive .tick input, store + 1)
    | .undefined, input => fun store => if limit = some store then _root_.Part.none else .some (input, store)

private theorem feedbackMember (limit : Option Nat) (wire store : Nat) (enabled : limit ≠ some store) :
    Eval (feedbackPrimitives limit) (.call callee (args 1 wire)) store (.returned (stateValue wire) store) := by
  refine .call ?_
  rw [openedMember]
  refine Eval.bind (node := gammaNode) (value := stateValue wire) (middle := store)
    (.gamma (tag := (1 : Fin 2)) ?_) (.ret _ _ _ _)
  refine Eval.bind (node := undefinedNode) (value := stateValue wire) (middle := store)
    (.primitive (undefinedSite wire) ?_) (.ret _ _ _ _)
  change (stateValue wire, store) ∈ (if limit = some store then _root_.Part.none
    else _root_.Part.some (stateValue wire, store))
  rw [ite_eq_right enabled]
  exact _root_.Part.mem_some _

private theorem feedbackActivation (limit : Option Nat) (wire store : Nat)
    (enabled : limit ≠ some (store + 1)) :
    Feedback.Iteration (feedbackPrimitives limit) loopBody (carriedValues 1 wire, store)
      (carriedValues 1 (wire + 1), store + 1) := by
  refine ⟨.control 1, ?_, rfl⟩
  refine Eval.bind (node := tickNode) (.primitive { tickSite with input := stateValue wire }
    (_root_.Part.mem_some _)) ?_
  exact .bind (node := callNode) (.apply (fn := fn) (feedbackMember limit (wire + 1) (store + 1) enabled))
    (.ret _ _ _ _)

private def restartAt (wire store : Nat) : Feedback.Restart machine Nat :=
  ⟨carried, [answer, answer], loopBody, carriedValues 1 wire, store⟩

private def savedParent : Descent.Pending machine carried answer :=
  .bind (past := []) afterLoop (carriedValues 1 7) PUnit.unit .empty

private theorem reachLoop {limit : Option Nat} {wire store : Nat}
    (iterations : ReflTransGen (Feedback.Iteration (feedbackPrimitives limit) loopBody)
      (carriedValues 1 7, 20) (carriedValues 1 wire, store)) :
    Feedback.Reaches (feedbackPrimitives limit) (entry 1) 20 (restartAt wire store) savedParent := by
  refine .call ?_
  rw [openedDriver]
  exact .inside (node := loopNode) (.theta (.restart iterations))

private theorem productiveRoot : Feedback.Productive (feedbackPrimitives none) (entry 1) 20 := by
  refine ⟨restartAt 7 20, savedParent, reachLoop .refl, ?_⟩
  refine ⟨fun n => (carriedValues 1 (7 + n), 20 + n), rfl, fun n => ?_⟩
  exact feedbackActivation none (7 + n) (20 + n) (by simp)

example : InfiniteTrace (Step (feedbackPrimitives none)) ⟨start (entry 1), 20⟩ :=
  productiveRoot.infinite .halt

private def cutoff : Option Nat := some 23

private theorem reachedThirdIteration :
    Feedback.Reaches (feedbackPrimitives cutoff) (entry 1) 20 (restartAt 9 22) savedParent :=
  reachLoop ((ReflTransGen.single (feedbackActivation cutoff 7 20 (by decide))).tail
    (feedbackActivation cutoff 8 21 (by decide)))

private def thirdBodyFrames : Descent.Pending machine answer (Theta.BodyResults carried) :=
  .bind (past := [answer]) afterCall (carriedValues 1 9) (stateValue 10, PUnit.unit) <|
    .bind (past := []) afterGamma (args 1 10) PUnit.unit <|
      .bind (past := []) afterUndefined (stateValue 10) PUnit.unit .empty

private def thirdBodyFrame : Stack machine (Theta.BodyResults carried) answer :=
  .loop loopBody (savedParent.push .halt)

private theorem cutoffBody :
    Eval (feedbackPrimitives cutoff) (.region loopBody (carriedValues 1 9) PUnit.unit) 22
      (.blocked (undefinedSite 10) thirdBodyFrames 23) := by
  refine Eval.bind (node := tickNode) (.primitive { tickSite with input := stateValue 9 }
    (_root_.Part.mem_some _)) ?_
  refine Eval.bindBlocked (node := callNode) (.apply (fn := fn) (.call ?_))
  change Eval (feedbackPrimitives cutoff) (Job.openClosure machine callee (args 1 10)) 23 _
  rw [openedMember]
  exact .bindBlocked (node := gammaNode) (.gamma (tag := (1 : Fin 2))
    (.bindBlocked (node := undefinedNode) (.primitiveBlocked (undefinedSite 10) 23 rfl)))

private def cutoffEndpoint : Config machine Nat answer :=
  ⟨.eval (undefinedSite 10).job (thirdBodyFrames.push thirdBodyFrame), 23⟩

example : Descent.stackDepth (thirdBodyFrames.push thirdBodyFrame) = 5 := rfl

private theorem cutoffObserved :
    ReflTransGen (Step (feedbackPrimitives cutoff)) ⟨start (entry 1), 20⟩ cutoffEndpoint ∧
      cutoffEndpoint.Blocked (feedbackPrimitives cutoff) := by
  have enters : Step (feedbackPrimitives cutoff) ((restartAt 9 22).config (savedParent.push .halt))
      ⟨.eval (.region loopBody (carriedValues 1 9) PUnit.unit) thirdBodyFrame, 22⟩ :=
    .of_next_some rfl
  exact ⟨((reachedThirdIteration.steps .halt).tail enters).trans (cutoffBody.steps thirdBodyFrame),
    cutoffBody.blocks thirdBodyFrame⟩

example : ∃ site pending, Eval (feedbackPrimitives cutoff) (entry 1) 20 (.blocked site pending 23) ∧
    cutoffEndpoint.control = .eval site.job (pending.push .halt) :=
  (blocked_iff_path (target := cutoffEndpoint)).mpr cutoffObserved

example : ¬ InfiniteTrace (Step (feedbackPrimitives cutoff)) ⟨start (entry 1), 20⟩ :=
  no_infinite_of_reaches_blocked cutoffObserved.1 cutoffObserved.2

example : ¬ Feedback.Productive (feedbackPrimitives cutoff) (entry 1) 20 :=
  fun productive => productive.no_block .halt cutoffObserved.1 cutoffObserved.2

-- A linked φ member finishes a call to its captured helper and then
-- recursively calls itself with a state-changing suffix still pending.
private abbrev recursionArgs := callable :: callable :: fn.args

private def descendTickNode : NestedTheta.Node (Instruction Op) recursionArgs [] answer :=
  ⟨answer, .base (.simple (.primitive .tick)), .cons (.arg (.tail (.tail (.tail .head)))) .nil,
    fun i => i.elim0⟩

private def helperNode : NestedTheta.Node (Instruction Op) recursionArgs [answer] answer :=
  ⟨carried, .base (.simple (.apply fn)), .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head)))
    (.cons (.output (0 : Fin 1) .head) .nil)), fun i => i.elim0⟩

private def descendNode : NestedTheta.Node (Instruction Op) recursionArgs [answer, answer] answer :=
  ⟨carried, .base (.simple (.apply fn)), .cons (.arg .head) (.cons (.arg (.tail (.tail .head)))
    (.cons (.output (1 : Fin 2) .head) .nil)), fun i => i.elim0⟩

private def suffixTickNode : NestedTheta.Node (Instruction Op) recursionArgs [answer, answer, answer] answer :=
  ⟨answer, .base (.simple (.primitive .tick)), .cons (.output (2 : Fin 3) .head) .nil, fun i => i.elim0⟩

private def descentSuffix :
    NestedTheta.Term (Instruction Op) recursionArgs [answer, answer, answer] [answer] answer :=
  .bind suffixTickNode (fun i => i.elim0) (.ret (.cons (.output (3 : Fin 4) .head) .nil))

private def descentBody :
    NestedTheta.Term (Instruction Op) recursionArgs [] [answer, answer, answer, answer] answer :=
  .bind descendTickNode (fun i => i.elim0) <| .bind helperNode (fun i => i.elim0) <|
    .bind descendNode (fun i => i.elim0) descentSuffix

private def descentMember : LambdaTerm Op [callable, callable] [] fn :=
  ⟨[callable, callable], .cons (.arg (.tail .head)) (.cons (.arg .head) .nil),
    [answer, answer, answer, answer], descentBody⟩

private def descentGroup : PhiTerm Op [] [[callable]] [fn] :=
  ⟨[callable], .cons (.output (0 : Fin 1) .head) .nil, .cons descentMember .nil⟩

private def descentModule : OmegaTerm Op [] [callable, callable] [[callable], [callable]] :=
  ⟨.bind (.phi group) <| .bind (.phi descentGroup) <|
    .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))⟩

private def descentExports : Tuple machine.Val [callable, callable] :=
  Recursive.linkGraph machine 51 descentModule.toGraph .nil

private def descentHelper : machine.Val callable := descentExports.get .head
private def descentCallee : machine.Val callable := descentExports.get (.tail .head)

private def descentInputs (wire : Nat) : Tuple machine.Val recursionArgs :=
  .cons descentCallee (.cons descentHelper (args 0 wire))

private theorem descentHelperOpened (wire : Nat) :
    Job.openClosure machine descentHelper (args 0 wire) = .region memberBody (args 0 wire) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (args 0 wire) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph memberBody)

private theorem descentOpened (wire : Nat) :
    Job.openClosure machine descentCallee (args 0 wire) = .region descentBody (descentInputs wire) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (descentInputs wire) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph descentBody)

private theorem descentHelperReturns (wire store : Nat) :
    Eval primitives (.call descentHelper (args 0 wire)) store (.returned (stateValue wire) store) := by
  refine .call ?_
  rw [descentHelperOpened]
  exact .bind (node := gammaNode) (.gamma (tag := (0 : Fin 2)) (.ret _ _ _ _)) (.ret _ _ _ _)

private def descentEntry (wire store : Nat) : CallDescent.Entry machine Nat :=
  ⟨⟨answer, ⟨fn.args, descentCallee, args 0 wire⟩⟩, store⟩

private def descentPending (wire : Nat) : Descent.Pending machine answer answer :=
  .bind (past := [answer, answer]) descentSuffix (descentInputs wire)
    (stateValue (wire + 1), (stateValue (wire + 1), PUnit.unit)) .empty

private theorem descentPrefix (wire store : Nat) :
    CallDescent.Prefix primitives (descentEntry wire store).call.openBody store
      (descentEntry (wire + 1) (store + 1)) (descentPending wire) := by
  change CallDescent.Prefix primitives (Job.openClosure machine descentCallee (args 0 wire)) store _ _
  rw [descentOpened]
  refine .later (node := descendTickNode) (.primitive { tickSite with input := stateValue wire }
    (_root_.Part.mem_some _)) ?_
  refine .later (node := helperNode) (.apply (fn := fn) (descentHelperReturns (wire + 1) (store + 1))) ?_
  exact .inside (node := descendNode) (.apply (fn := fn) descentCallee (args 0 (wire + 1)) (store + 1))

private def descentRun : CallDescent.Run primitives where
  entry n := descentEntry (7 + n) (20 + n)
  pending n := descentPending (7 + n)
  reaches n := descentPrefix (7 + n) (20 + n)

private def descentHalt : Stack machine (descentRun.entry 0).call.results answer := .halt

example : InfiniteTrace (Step primitives) ⟨start (.call descentCallee (args 0 7)), 20⟩ :=
  descentRun.infinite descentHalt

-- The second selected recursive call sees two distinct live suffix frames.
-- Each earlier activation completed a helper call and kept its updated local.
example : ∃ (micro : Nat → Config machine Nat answer) (indices : Nat → Nat),
    CallDescent.Checkpoints descentRun descentHalt micro indices ∧
    micro (indices 2) = (descentEntry 9 22).config ((descentPending 8).push ((descentPending 7).push .halt)) := by
  obtain ⟨micro, indices, checked⟩ := descentRun.checkpoints descentHalt
  exact ⟨micro, indices, checked, checked.atEntry 2⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Tests
