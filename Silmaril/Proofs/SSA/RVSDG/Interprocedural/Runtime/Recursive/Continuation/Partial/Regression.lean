module

import Mathlib.Tactic.IntervalCases
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Thms
import Silmaril.Foundations.InfiniteTrace.Deterministic
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Thms
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

-- Compute the finite interval from the machine, with an Option presentation
-- of these concrete primitive actions for executable fixture stepping.
private def fixtureAction {ins outs : Ports T} (opcode : Op ins outs)
    (input : Tuple machine.Val ins) (store : Nat) : Option (Tuple machine.Val outs × Nat) :=
  match opcode with
  | .tick => some (machine.primitive .tick input, store + 1)
  | .undefined => none

private theorem fixtureAction_eq {ins outs : Ports T} (opcode : Op ins outs)
    (input : Tuple machine.Val ins) (store : Nat) :
    _root_.Part.ofOption (fixtureAction opcode input store) = (primitives.step opcode input).run store := by
  cases opcode <;> rfl

private def fixtureNext (source : Config machine Nat answer) : Option (Config machine Nat answer) :=
  match selectedPrimitive source.control with
  | some active =>
    (fixtureAction active.site.opcode active.site.input source.store).map
      fun (output, store) => ⟨.returned output active.stack, store⟩
  | none => source.control.next.map fun next => ⟨next, source.store⟩

private theorem fixtureNext_eq (source : Config machine Nat answer) :
    _root_.Part.ofOption (fixtureNext source) = source.next primitives := by
  unfold fixtureNext Config.next
  cases selectedPrimitive source.control with
  | none => rfl
  | some active =>
    have map_eq {A B : Type} (result : Option A) (f : A → B) :
        _root_.Part.ofOption (result.map f) = (_root_.Part.ofOption result).map f := by
      cases result with
      | none => exact (_root_.Part.map_none f).symm
      | some => rfl
    rw [map_eq, fixtureAction_eq]

-- The opened region is normalized once by the closure-opening equation.
-- Every later configuration is obtained by the fixture's actual next function.
private def descentTrace : Nat → Config machine Nat answer
  | 0 => (descentEntry 7 20).config .halt
  | 1 => ⟨.eval (.region descentBody (descentInputs 7) PUnit.unit) .halt, 20⟩
  | n + 2 => (fixtureNext (descentTrace (n + 1))).getD (descentTrace (n + 1))

private theorem descentTraceSteps (i : Nat) (before : i < 15) :
    Step primitives (descentTrace i) (descentTrace (i + 1)) := by
  apply Step.of_next_some
  rw [← fixtureNext_eq]
  have picked : fixtureNext (descentTrace i) = some (descentTrace (i + 1)) := by
    interval_cases i <;> try rfl
    change some (Config.mk (.eval (Job.openClosure machine descentCallee (args 0 7)) .halt) 20) =
      some (Config.mk (.eval (.region descentBody (descentInputs 7) PUnit.unit) .halt) 20)
    rw [descentOpened]
  rw [picked]
  rfl

private theorem descentTraceLive :
    Descent.BeforeReturn (fun i => (descentTrace i).control) 1 15 (.halt : Stack machine answer answer) := by
  intro i later before
  rintro ⟨value, returned⟩
  interval_cases i <;> cases returned

private theorem descentTraceEarlier : Descent.EarlierCallsReturn (fun i => (descentTrace i).control) 1 15 := by
  intro i later before params results callee arguments stack entered
  interval_cases i <;> try (solve | cases entered)
  cases entered
  exact ⟨12, by decide, by decide, _, rfl⟩

private theorem descentTraceNext :
    descentTrace 15 = (descentEntry 8 21).config ((descentPending 7).push .halt) := rfl

example : ∃ pending, CallDescent.Prefix primitives (descentEntry 7 20).call.openBody 20 (descentEntry 8 21) pending ∧
    pending.push (.halt : Stack machine answer answer) = (descentPending 7).push .halt :=
  CallDescent.entry_of_interval (fun i _ before => descentTraceSteps i before)
    (show descentTrace 0 = (descentEntry 7 20).config .halt from rfl)
    descentTraceNext (by decide) descentTraceLive descentTraceEarlier

private def firstChildFrame : Stack machine answer answer := (descentPending 7).push .halt

private theorem noStepAtHalt (value : Tuple machine.Val answer) (store : Nat) (next : Config machine Nat answer) :
    ¬ Step primitives ⟨.returned value .halt, store⟩ next :=
  _root_.Part.notMem_none next

private theorem firstChildSuffix (value : Tuple machine.Val answer) (store : Nat) :
    ReflTransGen (Step primitives) ⟨.returned value firstChildFrame, store⟩
      ⟨.returned (machine.primitive .tick value) .halt, store + 1⟩ := by
  cases value with
  | cons value rest =>
    cases rest
    cases value with
    | state n =>
      let saved : Locals machine.Val [answer, answer] := (stateValue 8, (stateValue 8, PUnit.unit))
      have suffix : Eval primitives (.region descentSuffix (descentInputs 7) (saved.snoc (stateValue n))) store
          (.returned (stateValue (Nat.succ n)) (store + 1)) := by
        exact Eval.bind (node := suffixTickNode) (value := stateValue (Nat.succ n)) (middle := store + 1)
          (.primitive { tickSite with input := stateValue n } (_root_.Part.mem_some _)) (.ret _ _ _ _)
      exact (suffix.steps .halt).head (.of_next_some rfl)

private theorem liveFirstChild (micro : Nat → Config machine Nat answer)
    (steps : ∀ i, Step primitives (micro i) (micro (i + 1))) :
    CallDescent.Extraction.LiveFrom micro 15 firstChildFrame := by
  rintro i _ ⟨value, popped⟩
  have actual : micro i = ⟨.returned value firstChildFrame, (micro i).store⟩ := by
    rw [← popped]
  have infinite : InfiniteTrace (Step primitives) (micro i) := by
    refine ⟨fun j => micro (i + j), by simp, fun j => ?_⟩
    simpa only [Nat.add_assoc] using steps (i + j)
  exact RightUnique.not_infinite_of_final (R := Step primitives) (fun _ _ _ left right => _root_.Part.mem_unique left right)
    (firstChildSuffix value (micro i).store) (noStepAtHalt _ _) (actual ▸ infinite)

-- The first nonreturning child is extracted from the actual infinite
-- stream. Its finite prefix is calculated directly by descentTrace.
example : ∃ (micro : Nat → Config machine Nat answer) (child : CallDescent.Entry machine Nat)
    (pending : Descent.Pending machine child.call.results answer),
    CallDescent.Extraction.FirstChild primitives (descentEntry 7 20) .halt micro 0 15 child pending ∧
      micro 15 = (descentEntry 8 21).config firstChildFrame := by
  obtain ⟨micro, atRoot, steps⟩ := descentRun.infinite descentHalt
  have align (i : Nat) (before : i ≤ 15) : micro i = descentTrace i := by
    induction i with
    | zero => exact atRoot
    | succ i ih =>
      exact _root_.Part.mem_unique (steps i) ((ih (by omega)).symm ▸ descentTraceSteps i (by omega))
  have atChild : micro 15 = (descentEntry 8 21).config firstChildFrame :=
    (align 15 (by decide)).trans descentTraceNext
  have candidate : CallDescent.Extraction.NonreturningCallAt micro 15 :=
    ⟨_, _, atChild, liveFirstChild micro steps⟩
  have rootLive : CallDescent.Extraction.LiveFrom micro 0 (.halt : Stack machine answer answer) := by
    rintro i _ ⟨value, popped⟩
    have actual : micro i = ⟨.returned value .halt, (micro i).store⟩ := by rw [← popped]
    exact noStepAtHalt value (micro i).store _ (actual ▸ steps i)
  obtain ⟨finish, child, pending, extracted⟩ :=
    CallDescent.Extraction.first_child steps atRoot rootLive ⟨15, by decide, candidate⟩
  have bound := extracted.minimal 15 (by decide) candidate
  have later := extracted.later
  have exactFinish : finish = 15 := by
    by_contra wrong
    have earlierEntry : (descentTrace finish).control = (child.config (pending.push descentHalt)).control :=
      congrArg Config.control ((align finish bound).symm.trans extracted.atEntry)
    rcases child with ⟨⟨results, ⟨params, callee, arguments⟩⟩, store⟩
    obtain ⟨stop, after, before, returned⟩ := descentTraceEarlier finish (by omega) (by omega)
      callee arguments (pending.push descentHalt) earlierEntry
    apply extracted.live stop (Nat.le_of_lt after)
    change Continuation.Feedback.atReturn _ (micro stop).control
    rw [align stop (by omega)]
    exact returned
  exact ⟨micro, child, pending, exactFinish ▸ extracted, atChild⟩

private def feedbackOnlyTick : NestedTheta.Node (Instruction Op) fn.args [] answer :=
  ⟨answer, .base (.simple (.primitive .tick)), .cons (.arg (.tail .head)) .nil, fun i => i.elim0⟩

private def feedbackOnlyRest : NestedTheta.Term (Instruction Op) fn.args [answer] [] (Theta.BodyResults fn.args) :=
  .ret (.cons (.arg .head) (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)))

private def feedbackOnlyBody : NestedTheta.Term (Instruction Op) fn.args [] [answer] (Theta.BodyResults fn.args) :=
  .bind feedbackOnlyTick (fun i => i.elim0) feedbackOnlyRest

private def feedbackOnlyNode : NestedTheta.Node (Instruction Op) fn.args [] fn.args :=
  NestedTheta.thetaVertex [answer]

private def feedbackOnlySuffix : NestedTheta.Term (Instruction Op) fn.args [fn.args] [] answer :=
  .ret (.cons (.output (0 : Fin 1) (.tail .head)) .nil)

private def feedbackOnlyTerm : NestedTheta.Term (Instruction Op) fn.args [] [fn.args] answer :=
  .bind feedbackOnlyNode (fun _ => feedbackOnlyBody) feedbackOnlySuffix

private def feedbackOnlyModule : OmegaTerm Op [] [callable] [[callable]] :=
  ⟨.bind (.lambda ⟨[], .nil, [fn.args], feedbackOnlyTerm⟩) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def feedbackOnlyCallee : machine.Val callable :=
  (Recursive.linkGraph machine 61 feedbackOnlyModule.toGraph .nil).get .head

private theorem feedbackOnlyOpened :
    Job.openClosure machine feedbackOnlyCallee (args 1 7) = .region feedbackOnlyTerm (args 1 7) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (args 1 7) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph feedbackOnlyTerm)

private def feedbackOnlyEntry : CallDescent.Entry machine Nat :=
  ⟨⟨answer, ⟨fn.args, feedbackOnlyCallee, args 1 7⟩⟩, 20⟩

private def feedbackOnlyParent : Stack machine fn.args answer :=
  .resume (past := []) feedbackOnlySuffix (args 1 7) PUnit.unit .halt

private def feedbackOnlyPhase (iteration phase : Nat) : Config machine Nat answer :=
  let input := args 1 (7 + iteration)
  let store := 20 + iteration
  let value := stateValue (7 + iteration + 1)
  let loop := Stack.loop feedbackOnlyBody feedbackOnlyParent
  let saved := Stack.resume (past := []) feedbackOnlyRest input PUnit.unit loop
  match phase with
  | 0 => ⟨.eval (.iteration feedbackOnlyBody input) feedbackOnlyParent, store⟩
  | 1 => ⟨.eval (.region feedbackOnlyBody input PUnit.unit) loop, store⟩
  | 2 => ⟨.eval (.node (.base (.simple (.primitive .tick))) (fun i => i.elim0) (fun i => i.elim0)
    (stateValue (7 + iteration))) saved, store⟩
  | 3 => ⟨.returned value saved, store + 1⟩
  | 4 => ⟨.eval (.region feedbackOnlyRest input (value, PUnit.unit)) loop, store + 1⟩
  | _ => ⟨.returned (.cons (.control 1) (args 1 (7 + iteration + 1))) loop, store + 1⟩

-- Explicit actual steps, with one tick and one restart in each cycle.
private def feedbackOnlyStream : Nat → Config machine Nat answer
  | 0 => feedbackOnlyEntry.config .halt
  | 1 => ⟨.eval (.region feedbackOnlyTerm (args 1 7) PUnit.unit) .halt, 20⟩
  | 2 => ⟨.eval (.node (.theta fn.args) (fun _ => [answer]) (fun _ => feedbackOnlyBody) (args 1 7))
    feedbackOnlyParent, 20⟩
  | n + 3 => feedbackOnlyPhase (n / 6) (n % 6)

private theorem feedbackOnlySteps (i : Nat) :
    Step primitives (feedbackOnlyStream i) (feedbackOnlyStream (i + 1)) := by
  cases i with
  | zero =>
    apply Step.of_next_some
    change _root_.Part.some (Config.mk (.eval (Job.openClosure machine feedbackOnlyCallee (args 1 7)) .halt) 20) =
      _root_.Part.some (Config.mk (.eval (.region feedbackOnlyTerm (args 1 7) PUnit.unit) .halt) 20)
    rw [feedbackOnlyOpened]
  | succ i =>
    cases i with
    | zero => exact .of_next_some rfl
    | succ i =>
      cases i with
      | zero => exact .of_next_some rfl
      | succ n =>
        change Step primitives (feedbackOnlyPhase (n / 6) (n % 6))
          (feedbackOnlyPhase ((n + 1) / 6) ((n + 1) % 6))
        have phases : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
        rcases phases with h | h | h | h | h | h
        all_goals
          first
          | have nextRound : (n + 1) / 6 = n / 6 := by omega
            rw [nextRound, show (n + 1) % 6 = n % 6 + 1 by omega, h]
            exact .of_next_some rfl
          | rw [show (n + 1) / 6 = n / 6 + 1 by omega, show (n + 1) % 6 = 0 by omega, h]
            exact .of_next_some rfl

private theorem feedbackOnlyNoLaterCalls (i : Nat) (later : 0 < i) :
    Descent.Entry.ofState (feedbackOnlyStream i).control = none := by
  cases i with
  | zero => cases later
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ n =>
        change Descent.Entry.ofState (feedbackOnlyPhase (n / 6) (n % 6)).control = none
        have small : n % 6 < 6 := Nat.mod_lt _ (by decide)
        generalize n % 6 = phase at small ⊢
        interval_cases phase <;> rfl

example : CallDescent.Extraction.HasFeedback primitives feedbackOnlyStream 1 := by
  apply CallDescent.Extraction.feedback_of_live (begin := 0) feedbackOnlySteps
    (caller := feedbackOnlyEntry) (base := .halt) rfl
  · rintro i _ ⟨value, popped⟩
    have actual : feedbackOnlyStream i = ⟨.returned value .halt, (feedbackOnlyStream i).store⟩ := by rw [← popped]
    exact noStepAtHalt value (feedbackOnlyStream i).store _ (actual ▸ feedbackOnlySteps i)
  · rintro i later ⟨entry, frame, atCall, _⟩
    have notCall := feedbackOnlyNoLaterCalls i later
    rw [atCall] at notCall
    rcases entry with ⟨⟨_, ⟨_, _, _⟩⟩, _⟩
    cases notCall

private def descentRoot : CallDescent.Entry machine Nat :=
  Divergence.linkedEntry machine 51 descentModule.toGraph .nil (.tail .head) (args 0 7) 20

-- Build the descent certificate independently and exercise replay.
example : Divergence.Diverges primitives descentRoot := .inl ⟨descentRun, rfl⟩

example : InfiniteTrace (Step primitives) ⟨start (.call descentCallee (args 0 7)), 20⟩ :=
  (Divergence.linked_diverges_iff (primitives := primitives) 51 descentModule.toGraph .nil
    (.tail .head) (args 0 7) 20).mp (.inl ⟨descentRun, rfl⟩)

example : Divergence.Diverges primitives descentRoot :=
  Divergence.diverges_iff_infinite.mpr (descentRun.infinite descentHalt)

private def feedbackAt (callee : machine.Val callable) : CallDescent.Entry machine Nat :=
  ⟨⟨answer, ⟨fn.args, callee, args 1 7⟩⟩, 20⟩

private theorem feedbackOnlyRuns :
    Feedback.Run primitives feedbackOnlyBody (args 1 7, 20) := by
  refine ⟨fun n => (args 1 (7 + n), 20 + n), rfl, fun n => ?_⟩
  refine ⟨.control 1, ?_, rfl⟩
  exact Eval.bind (node := feedbackOnlyTick) (value := stateValue (7 + n + 1)) (middle := 20 + n + 1)
    (.primitive { tickSite with input := stateValue (7 + n) } (_root_.Part.mem_some _)) (.ret _ _ _ _)

private theorem feedbackRouteAt (callee : machine.Val callable)
    (opened : Job.openClosure machine callee (args 1 7) = .region feedbackOnlyTerm (args 1 7) PUnit.unit)
    (stack : Stack machine answer answer) : Divergence.FeedbackRoute primitives (feedbackAt callee) stack := by
  let target : Feedback.Restart machine Nat := ⟨fn.args, [answer], feedbackOnlyBody, args 1 7, 20⟩
  let pending : Descent.Pending machine fn.args answer :=
    .bind (past := []) feedbackOnlySuffix (args 1 7) PUnit.unit .empty
  refine .restart (target := target) (pending := pending) ?_ feedbackOnlyRuns
  change Feedback.Reaches primitives (Job.openClosure machine callee (args 1 7)) 20 target _
  rw [opened]
  exact .inside (node := feedbackOnlyNode) (.theta (.restart (input := (args 1 7, 20)) (current := (args 1 7, 20)) .refl))

private def feedbackCallNode : NestedTheta.Node (Instruction Op) carried [] answer :=
  ⟨carried, .base (.simple (.apply fn)), .cons (.arg .head) (.cons (.arg (.tail .head))
    (.cons (.arg (.tail (.tail .head))) .nil)), fun i => i.elim0⟩

private def feedbackCallSuffix : NestedTheta.Term (Instruction Op) carried [answer] [] answer :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def feedbackCallTerm : NestedTheta.Term (Instruction Op) carried [] [answer] answer :=
  .bind feedbackCallNode (fun i => i.elim0) feedbackCallSuffix

private def feedbackRootModule : OmegaTerm Op [] [callable, callable] [[callable], [callable]] :=
  ⟨.bind (.lambda ⟨[], .nil, [fn.args], feedbackOnlyTerm⟩) <|
    .bind (.lambda ⟨[callable], .cons (.output (0 : Fin 1) .head) .nil, [answer], feedbackCallTerm⟩) <|
      .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))⟩

private def feedbackRootExports : Tuple machine.Val [callable, callable] :=
  Recursive.linkGraph machine 62 feedbackRootModule.toGraph .nil

private def feedbackRootHelper : machine.Val callable := feedbackRootExports.get .head
private def feedbackRootCallee : machine.Val callable := feedbackRootExports.get (.tail .head)
private def feedbackRoot : CallDescent.Entry machine Nat :=
  Divergence.linkedEntry machine 62 feedbackRootModule.toGraph .nil (.tail .head) (args 1 7) 20

private theorem feedbackRootOpened :
    Job.openClosure machine feedbackRootCallee (args 1 7) =
      .region feedbackCallTerm (.cons feedbackRootHelper (args 1 7)) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (.cons feedbackRootHelper (args 1 7)) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph feedbackCallTerm)

private theorem feedbackRootHelperOpened :
    Job.openClosure machine feedbackRootHelper (args 1 7) = .region feedbackOnlyTerm (args 1 7) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (args 1 7) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph feedbackOnlyTerm)

-- Independently specify one nested call with a saved suffix before θ.
private theorem feedbackRootDiverges : Divergence.Diverges primitives feedbackRoot := by
  apply Or.inr
  let pending : Descent.Pending machine answer answer :=
    .bind (past := []) feedbackCallSuffix (.cons feedbackRootHelper (args 1 7)) PUnit.unit .empty
  refine .call (child := feedbackAt feedbackRootHelper) (pending := pending) ?_
    (feedbackRouteAt feedbackRootHelper feedbackRootHelperOpened (pending.push .halt))
  change CallDescent.Prefix primitives (Job.openClosure machine feedbackRootCallee (args 1 7)) 20 _ _
  rw [feedbackRootOpened]
  exact .inside (node := feedbackCallNode) (.apply (fn := fn) feedbackRootHelper (args 1 7) 20)

example : InfiniteTrace (Step primitives) ⟨start (.call feedbackRootCallee (args 1 7)), 20⟩ :=
  (Divergence.linked_diverges_iff (primitives := primitives) 62 feedbackRootModule.toGraph .nil
    (.tail .head) (args 1 7) 20).mp feedbackRootDiverges

-- Exercise θ projection from the separately checked actual machine stream.
example : Divergence.Diverges primitives
    (Divergence.linkedEntry machine 61 feedbackOnlyModule.toGraph .nil .head (args 1 7) 20) :=
  (Divergence.linked_diverges_iff (primitives := primitives) 61 feedbackOnlyModule.toGraph .nil
    .head (args 1 7) 20).mpr ⟨feedbackOnlyStream, rfl, feedbackOnlySteps⟩

example : ¬ Divergence.Diverges primitives
    (Divergence.linkedEntry machine 47 linked.toGraph .nil (.tail .head) (args 1 7) 20) :=
  Divergence.not_diverges_of_blocked (blockRoot.steps .halt) (blockRoot.blocks .halt)

private def outcomeEntry (selector : Fin 2) : CallDescent.Entry machine Nat :=
  Divergence.linkedEntry machine 47 linked.toGraph .nil (.tail .head) (args selector 7) 20

private theorem outcomeReturned : Classification.Returns primitives (outcomeEntry 0) :=
  ⟨stateValue 8, 21, returnRoot⟩

private theorem outcomeBlocked : Classification.Blocks primitives (outcomeEntry 1) :=
  ⟨undefinedSite 8, savedFrames, 21, blockRoot⟩

private theorem outcomeDiverges : Divergence.Diverges (feedbackPrimitives none) (outcomeEntry 1) :=
  Divergence.diverges_iff_infinite.mpr (productiveRoot.infinite .halt)

-- The same linked export returns through γ arm 0. With arm 1 it
-- either blocks on the selected action or feeds back indefinitely,
-- depending on the interpretation of that primitive.
example : Classification.Returns primitives (outcomeEntry 0) ∧
    ¬ Classification.Blocks primitives (outcomeEntry 0) ∧
    ¬ Divergence.Diverges primitives (outcomeEntry 0) := by
  have classified := Classification.linked_trichotomy (primitives := primitives)
    47 linked.toGraph .nil (.tail .head) (args 0 7) 20
  exact ⟨outcomeReturned, classified.return_exclusive outcomeReturned⟩

example : Classification.Blocks primitives (outcomeEntry 1) ∧
    ¬ Classification.Returns primitives (outcomeEntry 1) ∧
    ¬ Divergence.Diverges primitives (outcomeEntry 1) := by
  have classified := Classification.linked_trichotomy (primitives := primitives)
    47 linked.toGraph .nil (.tail .head) (args 1 7) 20
  exact ⟨outcomeBlocked, fun returned => (classified.return_exclusive returned).1 outcomeBlocked,
    classified.block_excludes_divergence outcomeBlocked⟩

example : Divergence.Diverges (feedbackPrimitives none) (outcomeEntry 1) ∧
    ¬ Classification.Returns (feedbackPrimitives none) (outcomeEntry 1) ∧
    ¬ Classification.Blocks (feedbackPrimitives none) (outcomeEntry 1) := by
  have classified := Classification.linked_trichotomy (primitives := feedbackPrimitives none)
    47 linked.toGraph .nil (.tail .head) (args 1 7) 20
  exact ⟨outcomeDiverges, fun returned => (classified.return_exclusive returned).2 outcomeDiverges,
    fun blocked => classified.block_excludes_divergence blocked outcomeDiverges⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Tests
