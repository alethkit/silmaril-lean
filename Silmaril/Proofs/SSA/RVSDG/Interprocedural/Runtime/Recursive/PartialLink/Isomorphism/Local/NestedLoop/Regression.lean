module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Tests

open SingleTheta (Carries FeedbackPair)

open Continuation.Partial
open Continuation.Descent (Pending)
open Isomorphism.Invocation (request)
open PartialLink.Invocation (start_linked)
open Relation (ReflTransGen TransGen)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev carried : Ports T := [.control 2, num]
private abbrev bodyResults : Ports T := Theta.BodyResults carried
private abbrev outerCarry : Ports T := .control 2 :: carried
private abbrev results : Ports T := [num, num]
private abbrev fn : Function Unit Unit := ⟨outerCarry, results⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit where
  | advance : Op carried bodyResults

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .advance, input => .cons (.control 0) input

private def carry (mode : Fin 2) (n : Nat) : Tuple machine.Val carried :=
  .cons (.control mode) (.cons (.data n) .nil)

private def output (n original : Nat) : Tuple machine.Val results :=
  .cons (.data n) (.cons (.data original) .nil)

private def bodyOut (selector mode : Fin 2) (n : Nat) : Tuple machine.Val bodyResults :=
  .cons (.control selector) (carry mode n)

private def action (mode : Fin 2) (n store : Nat) : _root_.Part (Tuple machine.Val bodyResults × Nat) :=
  if mode.val = 1 then
    if n = 0 then .some (bodyOut 0 mode (n + 1), store + 3)
    else .some (bodyOut 1 mode (n + 1), store + 3)
  else if n = 1 then .none
  else if n = 0 then .some (bodyOut 1 mode (n + 1), store + 3)
  else .some (bodyOut 0 mode (n + 1), store + 3)

private def primitives : Primitives machine Nat where
  step
    | .advance, .cons (.control mode) (.cons (.data n) .nil) => action mode n

private theorem carry_related (mode : Fin 2) (n : Nat) : TupleRelated machine Eq (carry mode n) (carry mode n) :=
  .cons (.control mode) (.cons (ValueRelated.data (m := machine) (t := ()) n) .nil)

private theorem respects : ActionsRespect primitives Eq := by
  intro _ _ opcode _ _ related store
  cases opcode with
  | advance =>
    cases related with
    | cons control tail =>
      cases control with
      | control mode =>
        cases tail with
        | cons number tail =>
          cases number with
          | data n =>
            cases tail
            change ActionRelated machine Eq Nat bodyResults (action mode n store) (action mode n store)
            unfold action
            split
            · split
              · exact .returned (.cons (.control 0) (carry_related _ _)) _
              · exact .returned (.cons (.control 1) (carry_related _ _)) _
            · split
              · exact .undefined
              · split
                · exact .returned (.cons (.control 1) (carry_related _ _)) _
                · exact .returned (.cons (.control 0) (carry_related _ _)) _

private def initial {past : List (Ports T)} : Wires carried past carried :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

private def innerInitial : Wires outerCarry [] carried :=
  .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)

private def innerOutputs : Wires outerCarry [carried] (Theta.BodyResults outerCarry) :=
  .cons (.arg .head) (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head)
    (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def outerInitial : Wires outerCarry [] outerCarry :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))

private def outputs : Wires outerCarry [outerCarry] results :=
  .cons (.output (0 : Fin 1) (.tail (.tail .head))) (.cons (.arg (.tail (.tail .head))) .nil)

private def idle {past : List (Ports T)} : Node Op carried past [] :=
  emptyGamma (entry := []) (extra := 0) (.cons (.arg .head) .nil)

private def advance {past : List (Ports T)} : Node Op carried past bodyResults :=
  ⟨carried, .simple .advance, initial, fun i => i.elim0⟩

private def tailL : Wires carried [[], bodyResults] bodyResults :=
  .cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head))
    (.cons (.output (1 : Fin 2) (.tail (.tail .head))) .nil))

private def tailR : Wires carried [bodyResults, []] bodyResults :=
  .cons (.output (0 : Fin 2) .head) (.cons (.output (0 : Fin 2) (.tail .head))
    (.cons (.output (0 : Fin 2) (.tail (.tail .head))) .nil))

private def termL : Term Op carried [] [[], bodyResults] bodyResults :=
  .bind idle (fun _ => .ret .nil) (.bind advance (fun i => i.elim0) (.ret tailL))

private def termR : Term Op carried [] [bodyResults, []] bodyResults :=
  .bind advance (fun i => i.elim0) (.bind idle (fun _ => .ret .nil) (.ret tailR))

private abbrev left := termL.toGraph
private abbrev right := termR.toGraph
private def numbering : Renaming := .region (Equiv.swap 0 1) (fun _ _ => .identity)
private def positions : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

private theorem two {p : Fin 2 → Prop} (first : p 0) (second : p 1) (i : Fin 2) : p i :=
  Fin.cases first (Fin.cases second (fun j => j.elim0)) i

private theorem ordered : OrderedGraph numbering left right := by
  constructor
  · have labels : ∀ i, (left.nodes i).label = (right.nodes (positions i)).label := two rfl rfl
    refine .intro rfl rfl positions (two rfl rfl) labels (two rfl rfl) rfl ?_
    apply two
    · intro _
      exact .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0)
        (fun i => i.elim0) rfl (fun i => i.elim0)
    · intro i
      exact i.elim0
  · rw [Term.toTerm_toGraph, Term.toTerm_toGraph]
    refine Schedule.emptyLeft idle.inputs ?_
    refine Schedule.bind (Shape.simple Op.advance) initial initial rfl rfl (fun i => i.elim0) ?_
    exact .emptyRight idle.inputs (.ret tailL tailR rfl)

private theorem embeddedIso : NestedTheta.Graph.Isomorphic (Instruction Op)
    (embed left.toTerm).toGraph (embed right.toTerm).toGraph := by
  rw [Term.toTerm_toGraph, Term.toTerm_toGraph]
  have labels : ∀ i, ((embed termL).toGraph.nodes i).label =
      ((embed termR).toGraph.nodes (positions i)).label := two rfl rfl
  refine .intro rfl rfl positions labels (two rfl rfl) rfl ?_
  apply two
  · intro _
    exact .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0) rfl (fun i => i.elim0)
  · intro i
    exact i.elim0

private theorem innerIso : NestedTheta.Graph.Isomorphic (Instruction Op)
    (SingleTheta.code innerInitial left innerOutputs).toGraph
    (SingleTheta.code innerInitial right innerOutputs).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) (fun i => Fin.cases rfl (fun j => j.elim0) i)
    (fun i => Fin.cases rfl (fun j => j.elim0) i) rfl ?_
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  intro _
  exact embeddedIso

private abbrev innerL : Body Op outerCarry [carried] := SingleTheta.code innerInitial left innerOutputs
private abbrev innerR : Body Op outerCarry [carried] := SingleTheta.code innerInitial right innerOutputs

private def innerMap : Renaming := .region (Equiv.refl _) (fun _ _ => numbering)
private def outerMap : Renaming := .region (Equiv.refl _) (fun _ _ => innerMap)

private theorem admitted : Gamma.CodePair Op innerMap innerL innerR :=
  .theta innerInitial innerOutputs rfl ordered

private def lambdaL := code outerInitial innerL outputs
private def lambdaR := code outerInitial innerR outputs

private theorem outerIso : NestedTheta.Graph.Isomorphic (Instruction Op) lambdaL.toGraph lambdaR.toGraph := by
  refine .intro rfl rfl (Equiv.refl _) (fun i => Fin.cases rfl (fun j => j.elim0) i)
    (fun i => Fin.cases rfl (fun j => j.elim0) i) rfl ?_
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  intro _
  exact innerIso

private abbrev LambdaBody := NestedTheta.Term (Instruction Op) outerCarry [] [outerCarry] results

private def omega (body : LambdaBody) : OmegaTerm Op [] [fn.port] [[fn.port]] :=
  ⟨.bind (.lambda ⟨[], .nil, [outerCarry], body⟩) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def modulePositions : Fin 1 ≃ Fin 1 := Equiv.refl _

private theorem moduleIso : (omega lambdaL).toGraph.RenumberedBy (omega lambdaR).toGraph modulePositions :=
  ⟨fun i => Fin.cases (.lambda ⟨⟨rfl, rfl⟩, outerIso⟩) (fun j => j.elim0) i, rfl⟩

private theorem moduleSchedule : Ordered Op (renameVertex modulePositions) [] [fn.port]
    (omega lambdaL).toGraph.toTerm.region (omega lambdaR).toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, outerIso⟩) (.ret _ _)

private def callable (body : LambdaBody) : machine.Val fn.port :=
  .closure (.nil : Tuple machine.Val []) body.toGraph

private theorem linked (body : LambdaBody) :
    Links primitives 17 (omega body).toGraph .nil 20 (.linked (.cons (callable body) .nil) 20) :=
  .bind (values := .cons (callable body) .nil) (middle := 20) rfl (.ret _ _ _ _)

private def input (flag mode : Fin 2) (n : Nat) : Tuple machine.Val outerCarry := .cons (.control flag) (carry mode n)

private abbrev entry (body : LambdaBody) (flag mode : Fin 2) (n : Nat) :=
  request (m := machine) 17 (omega body).toGraph .nil .head (input flag mode n) 20

private def source (body : LambdaBody) (flag mode : Fin 2) (n : Nat) : Config machine Nat results :=
  ⟨Continuation.start (.call (callable body) (input flag mode n)), 20⟩

private theorem started (body : LambdaBody) (flag mode : Fin 2) (n : Nat) :
    (entry body flag mode n).start primitives = .ok (source body flag mode n) :=
  start_linked (request := entry body flag mode n) (linked body)

private theorem dispatch (flag mode : Fin 2) (n : Nat) :
    CallPair primitives Eq outerMap results (source lambdaL flag mode n) (source lambdaR flag mode n) := by
  have paired := link_then_invoke (mapping := outerMap) respects moduleIso moduleSchedule
    (fun i => by simp [renameVertex, modulePositions]) .nil .head (.cons (.control flag) (carry_related mode n)) 20
    (unitL := 17) (unitR := 17) (by
      intro exportsL exportsR post linkedL linkedR _
      cases outcome_unique linkedL (linked lambdaL)
      cases outcome_unique linkedR (linked lambdaR)
      exact .closure .nil outerInitial outputs rfl admitted)
  change DispatchPair primitives Eq (renameVertex modulePositions) outerMap results
    ((entry lambdaL flag mode n).start primitives) ((entry lambdaR flag mode n).start primitives) at paired
  rw [started, started] at paired
  cases paired with
  | invoked paired => exact paired

private def atCarry (mode : Fin 2) (n store : Nat) : Carries machine Eq Nat carried :=
  ⟨carry mode n, carry mode n, carry_related mode n, store⟩

private def advanceSite (mode : Fin 2) (n : Nat) : Site machine :=
  ⟨carried, bodyResults, .advance, fun i => i.elim0, fun i => embed (i.elim0), carry mode n⟩

private theorem idleEval {past : List (Ports T)} (locals : Locals machine.Val past)
    (mode : Fin 2) (n store : Nat) :
    Eval primitives (nodeJob idle (fun _ => .ret .nil) (carry mode n) locals) store (.returned .nil store) :=
  Eval.gamma (tag := mode) (cs := fun _ => []) (children := fun _ => .ret .nil)
    (Eval.ret (past := []) .nil .nil PUnit.unit store)

private theorem allOutputs (value : Tuple machine.Val bodyResults) :
    Tuple.cons (value.get .head)
      (.cons (value.get (.tail .head)) (.cons (value.get (.tail (.tail .head))) .nil)) = value := by
  cases value with
  | cons _ tail =>
    cases tail with
    | cons _ tail =>
      cases tail with
      | cons _ tail => cases tail; rfl

private theorem bodyReturnsL (mode : Fin 2) (n store : Nat)
    {result : Tuple machine.Val bodyResults} {next : Nat}
    (defined : (result, next) ∈ action mode n store) :
    Eval primitives (.region (embed left.toTerm) (carry mode n) PUnit.unit) store (.returned result next) := by
  rw [Term.toTerm_toGraph]
  refine Eval.bind (idleEval (past := []) PUnit.unit mode n store)
    (Eval.bind (middle := next) (value := result) (Eval.primitive (advanceSite mode n) defined) ?_)
  let locals := (Locals.snoc (past := []) (F := machine.Val) PUnit.unit .nil).snoc result
  have ran := Eval.ret (primitives := primitives) tailL (carry mode n) locals next
  rw [show tailL.read (carry mode n) locals = result from allOutputs result] at ran
  exact ran

private theorem bodyReturnsR (mode : Fin 2) (n store : Nat)
    {result : Tuple machine.Val bodyResults} {next : Nat}
    (defined : (result, next) ∈ action mode n store) :
    Eval primitives (.region (embed right.toTerm) (carry mode n) PUnit.unit) store (.returned result next) := by
  rw [Term.toTerm_toGraph]
  let prefixLocals := Locals.snoc (past := []) PUnit.unit result
  refine Eval.bind (middle := next) (value := result) (Eval.primitive (advanceSite mode n) defined)
    (Eval.bind (idleEval prefixLocals mode n next) ?_)
  have ran := Eval.ret (primitives := primitives) tailR (carry mode n) (prefixLocals.snoc .nil) next
  rw [show tailR.read (carry mode n) (prefixLocals.snoc .nil) = result from allOutputs result] at ran
  exact ran

private theorem feedback (mode : Fin 2) (n store : Nat)
    (defined : (bodyOut 1 mode (n + 1), store + 3) ∈ action mode n store) :
    FeedbackPair primitives left right (atCarry mode n store) (atCarry mode (n + 1) (store + 3)) :=
  ⟨⟨.control 1, bodyReturnsL mode n store defined, rfl⟩, ⟨.control 1, bodyReturnsR mode n store defined, rfl⟩⟩

private def outerInput (flag mode : Fin 2) (n store : Nat) : Carries machine Eq Nat outerCarry :=
  ⟨input flag mode n, input flag mode n, .cons (.control flag) (carry_related mode n), store⟩

/-- A whole outer activation can finish only after the inner θ exits.
Its selector comes from the original outer argument, and the returned
carry contains the inner θ's updated data. -/
private theorem completedInner (flag mode : Fin 2) (n store : Nat)
    (defined : (bodyOut 0 mode (n + 1), store + 3) ∈ action mode n store) :
    Eval primitives (.region innerL (input flag mode n) PUnit.unit) store
      (.returned (.cons (.control flag) (input flag mode (n + 1))) (store + 3)) ∧
    Eval primitives (.region innerR (input flag mode n) PUnit.unit) store
      (.returned (.cons (.control flag) (input flag mode (n + 1))) (store + 3)) :=
  ⟨.bind (node := Isomorphism.Invocation.loopVertex innerInitial [[], bodyResults])
      (.theta (.stop (bodyReturnsL mode n store defined) rfl)) (.ret innerOutputs _ _ _),
   .bind (node := Isomorphism.Invocation.loopVertex innerInitial [bodyResults, []])
      (.theta (.stop (bodyReturnsR mode n store defined) rfl)) (.ret innerOutputs _ _ _)⟩

private theorem outerStep (mode : Fin 2) (n store : Nat)
    (defined : (bodyOut 0 mode (n + 1), store + 3) ∈ action mode n store) :
    IterationPair primitives innerL innerR (outerInput 1 mode n store) (outerInput 1 mode (n + 1) (store + 3)) :=
  let ran := completedInner 1 mode n store defined
  ⟨⟨.control 1, ran.1, rfl⟩, ⟨.control 1, ran.2, rfl⟩⟩

private theorem outerStream : InfiniteTrace (IterationPair primitives innerL innerR) (outerInput 1 0 2 20) := by
  refine ⟨fun n => outerInput 1 0 (n + 2) (20 + 3 * n), rfl, ?_⟩
  intro n
  have sameStore : 20 + 3 * (n + 1) = 20 + 3 * n + 3 := by omega
  change IterationPair primitives innerL innerR (outerInput 1 0 (n + 2) (20 + 3 * n))
    (outerInput 1 0 ((n + 1) + 2) (20 + 3 * (n + 1)))
  rw [sameStore]
  apply outerStep
  have notOne : n + 2 ≠ 1 := by omega
  have notZero : n + 2 ≠ 0 := by omega
  unfold action
  rw [ite_eq_right (by decide : ¬ (0 : Fin 2).val = 1), ite_eq_right notOne, ite_eq_right notZero]
  exact _root_.Part.mem_some _

private theorem innerStream : InfiniteTrace (FeedbackPair primitives left right) (atCarry 1 1 23) := by
  refine ⟨fun n => atCarry 1 (n + 1) (23 + 3 * n), rfl, ?_⟩
  intro n
  have sameStore : 23 + 3 * (n + 1) = 23 + 3 * n + 3 := by omega
  change FeedbackPair primitives left right (atCarry 1 (n + 1) (23 + 3 * n))
    (atCarry 1 ((n + 1) + 1) (23 + 3 * (n + 1)))
  rw [sameStore]
  apply feedback
  have notZero : n + 1 ≠ 0 := by omega
  unfold action
  rw [ite_eq_left (by decide : (1 : Fin 2).val = 1), ite_eq_right notZero]
  exact _root_.Part.mem_some _

private def innerPending : Pending machine carried (Theta.BodyResults outerCarry) :=
  .bind (past := []) (.ret innerOutputs) (input 1 1 1) PUnit.unit .empty

private theorem innerEnteredL :
    Feedback.Reaches primitives (.region innerL (input 1 1 1) PUnit.unit) 23
      ⟨carried, [[], bodyResults], embed left.toTerm, (carry 1 1, 23)⟩ innerPending :=
  .inside (node := Isomorphism.Invocation.loopVertex innerInitial [[], bodyResults])
    (.theta (.restart (input := (carry 1 1, 23)) (current := (carry 1 1, 23)) .refl))

private theorem innerEnteredR :
    Feedback.Reaches primitives (.region innerR (input 1 1 1) PUnit.unit) 23
      ⟨carried, [bodyResults, []], embed right.toTerm, (carry 1 1, 23)⟩ innerPending :=
  .inside (node := Isomorphism.Invocation.loopVertex innerInitial [bodyResults, []])
    (.theta (.restart (input := (carry 1 1, 23)) (current := (carry 1 1, 23)) .refl))

private theorem innerProductive : Gamma.ProductivePair primitives Eq
    (.region innerL (input 1 1 1) PUnit.unit) (.region innerR (input 1 1 1) PUnit.unit) 23 :=
  .reached innerStream innerEnteredL innerEnteredR

private theorem outerOnce :
    IterationPair primitives innerL innerR (outerInput 1 1 0 20) (outerInput 1 1 1 23) :=
  outerStep 1 0 20 (_root_.Part.mem_some _)

/-- The inner activation becomes productive after one whole outer
restart. It excludes further unbounded completed outer restarts. -/
private theorem distinct :
    ¬ InfiniteTrace (IterationPair primitives innerL innerR) (outerInput 1 1 0 20) :=
  inner_excludes_outer (.single outerOnce) innerProductive

private def parent (flag mode : Fin 2) (n : Nat) : Continuation.Stack machine outerCarry results :=
  .resume (past := []) (.ret outputs) (input flag mode n) PUnit.unit .halt

private theorem firstOuterRestart :
    TransGen (Step primitives) (restart innerL outputs (input 1 0 2) (input 1 0 2, 20))
      (restart innerL outputs (input 1 0 2) (input 1 0 3, 23)) ∧
    TransGen (Step primitives) (restart innerR outputs (input 1 0 2) (input 1 0 2, 20))
      (restart innerR outputs (input 1 0 2) (input 1 0 3, 23)) :=
  (outerStep 0 2 20 (_root_.Part.mem_some _)).steps (parent 1 0 2) (parent 1 0 2)

private theorem openFixture (body : LambdaBody) (flag mode : Fin 2) (n : Nat) :
    Job.openClosure machine (callable body) (input flag mode n) =
      .region body (input flag mode n) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (input flag mode n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph body)

private theorem enterCall {sigs : List (Ports T)} {body : Body Op outerCarry sigs}
    {flag mode : Fin 2} {n : Nat} {target : Feedback.Restart machine Nat} {pending : Pending machine target.carried outerCarry}
    (reached : Feedback.Reaches primitives (.iteration body (input flag mode n)) 20 target pending) :
    Feedback.Reaches primitives (.call (callable (code outerInitial body outputs)) (input flag mode n)) 20 target
      (.bind (past := []) (.ret outputs) (input flag mode n) PUnit.unit pending) := by
  apply Feedback.Reaches.call
  rw [openFixture]
  exact .inside (node := Isomorphism.Invocation.loopVertex outerInitial sigs) (.theta reached)

/-- A certificate of infinitely many positive outer segments replays on
the actual left dispatch, then transports to the right dispatch. -/
private theorem outerCall : InfiniteTrace (Step primitives) (source lambdaR 1 0 2) := by
  apply (dispatch 1 0 2).infinite_iff.mp
  let target : Feedback.Restart machine Nat := ⟨outerCarry, [carried], innerL, (input 1 0 2, 20)⟩
  have run : Feedback.Run primitives innerL target.input :=
    InfiniteTrace.map (R := IterationPair primitives innerL innerR) (S := Feedback.Iteration primitives innerL)
      (fun current => (current.left, current.store)) (fun _ _ h => h.1) outerStream
  have arrived : Feedback.Reaches primitives (.iteration innerL (input 1 0 2)) 20 target .empty :=
    .restart (input := target.input) (current := target.input) .refl
  have productive : Feedback.Productive primitives (.call (callable lambdaL) (input 1 0 2)) 20 :=
    ⟨target, _, enterCall arrived, run⟩
  exact productive.infinite .halt

/-- A finite outer prefix enters the actual inner restart. The inner
feedback replays with the original outer suffix and loop frame pending. -/
private theorem innerCall : InfiniteTrace (Step primitives) (source lambdaR 1 1 0) := by
  apply (dispatch 1 1 0).infinite_iff.mp
  let target : Feedback.Restart machine Nat := ⟨carried, [[], bodyResults], embed left.toTerm, (carry 1 1, 23)⟩
  have run : Feedback.Run primitives (embed left.toTerm) target.input :=
    InfiniteTrace.map (R := FeedbackPair primitives left right) (S := Feedback.Iteration primitives (embed left.toTerm))
      (fun current => (current.left, current.store)) (fun _ _ h => h.1) innerStream
  have arrived : Feedback.Reaches primitives (.iteration innerL (input 1 1 0)) 20 target (.loop innerL innerPending) :=
    .iteration (current := (input 1 1 1, 23)) (.single outerOnce.1) innerEnteredL
  have productive : Feedback.Productive primitives (.call (callable lambdaL) (input 1 1 0)) 20 :=
    ⟨target, _, enterCall arrived, run⟩
  exact productive.infinite .halt

private theorem callEval {body : LambdaBody} {flag mode : Fin 2} {n : Nat}
    {outcome : Continuation.Partial.Outcome machine Nat results}
    (ran : Eval primitives (.region body (input flag mode n) PUnit.unit) 20 outcome) :
    Eval primitives (.call (callable body) (input flag mode n)) 20 outcome :=
  .call ((openFixture body flag mode n).symm ▸ ran)

private theorem replayExit {sigs : List (Ports T)} {body : Body Op outerCarry sigs}
    (ran : Eval primitives (.region body (input 0 0 2) PUnit.unit) 20
      (.returned (.cons (.control 0) (input 0 0 3)) 23)) :
    TerminalPath primitives (source (code outerInitial body outputs) 0 0 2) ⟨.returned (output 3 2) .halt, 23⟩ := by
  have bodyRan : Eval primitives (.region (code outerInitial body outputs) (input 0 0 2) PUnit.unit) 20
      (.returned (output 3 2) 23) :=
    .bind (node := Isomorphism.Invocation.loopVertex outerInitial sigs) (.theta (.stop ran rfl)) (.ret outputs _ _ _)
  exact ⟨(callEval bodyRan).steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩

/-- A completed inner activation can also exit the outer θ and wire the
updated data together with the original saved argument. -/
private theorem returnedCalls :
    TerminalPath primitives (source lambdaL 0 0 2) ⟨.returned (output 3 2) .halt, 23⟩ ∧
    TerminalPath primitives (source lambdaR 0 0 2) ⟨.returned (output 3 2) .halt, 23⟩ :=
  let ran := completedInner 0 0 2 20 (_root_.Part.mem_some _)
  ⟨replayExit ran.1, replayExit ran.2⟩

private def pendingL : Pending machine bodyResults bodyResults :=
  .bind (past := [[]]) (.ret tailL) (carry 0 1) (Locals.snoc (past := []) PUnit.unit .nil) .empty

private def pendingR : Pending machine bodyResults bodyResults :=
  .bind (past := []) (embed (.bind idle (fun _ => .ret .nil) (.ret tailR))) (carry 0 1) PUnit.unit .empty

private theorem blockedL :
    Local.BlockAt primitives left.toTerm (carry 0 1) PUnit.unit 23 (.here 1)
      (.blocked (advanceSite 0 1) pendingL 23) := by
  rw [Term.toTerm_toGraph]
  exact .later (idleEval (past := []) PUnit.unit 0 1 23)
    (Local.BlockAt.here (past := [[]]) Op.advance initial (carry 0 1)
      (Locals.snoc (past := []) PUnit.unit .nil) 23 rfl)

private theorem blockedR :
    Local.BlockAt primitives right.toTerm (carry 0 1) PUnit.unit 23 (.here 0)
      (.blocked (advanceSite 0 1) pendingR 23) := by
  rw [Term.toTerm_toGraph]
  exact Local.BlockAt.here (past := []) Op.advance initial (carry 0 1) PUnit.unit 23 rfl

private def stopped {sigs : List (Ports T)} (body : SingleTheta.Body Op carried sigs)
    (pending : Pending machine bodyResults bodyResults) : Gamma.Block machine Nat (Theta.BodyResults outerCarry) :=
  ⟨advanceSite 0 1, .bind (past := []) (.ret innerOutputs) (input 0 0 0) PUnit.unit
    (.loop (embed body.toTerm) pending), 23⟩

private theorem blockedActivation :
    Gamma.BlockPair primitives Eq innerMap innerL innerR (input 0 0 0) (input 0 0 0) 20
      (.theta (.here 1)) (.theta (.here 0)) (stopped left pendingL) (stopped right pendingR) :=
  .theta (first := atCarry 0 0 20) (current := atCarry 0 1 23) innerInitial innerOutputs rfl rfl rfl
    (.single (feedback 0 0 20 (_root_.Part.mem_some _))) (.here 1) (.same (carry_related 0 1)) blockedL blockedR

private theorem replayBlock {sigs : List (Ports T)} {body : Body Op outerCarry sigs}
    {stop : Gamma.Block machine Nat (Theta.BodyResults outerCarry)}
    (ran : Eval primitives (.region body (input 0 0 0) PUnit.unit) 20 stop.outcome) :
    TerminalPath primitives (source (code outerInitial body outputs) 0 0 0)
      ((blockOutcome body outputs (input 0 0 0) stop).atStack .halt) := by
  cases stop
  have blocked : Eval primitives (.region (code outerInitial body outputs) (input 0 0 0) PUnit.unit) 20
      (blockOutcome body outputs (input 0 0 0) _) :=
    .bindBlocked (node := Isomorphism.Invocation.loopVertex outerInitial sigs) (.theta (.loopBlocked ran))
  have call := callEval blocked
  exact ⟨call.steps .halt, fun _ => (call.blocks .halt).no_step⟩

/-- The relocated effect blocks after inner feedback at store 23 with
both live loop frames and their saved suffixes intact. -/
private theorem blockedCalls :
    TerminalPath primitives (source lambdaL 0 0 0)
      ((blockOutcome innerL outputs (input 0 0 0) (stopped left pendingL)).atStack .halt) ∧
    TerminalPath primitives (source lambdaR 0 0 0)
      ((blockOutcome innerR outputs (input 0 0 0) (stopped right pendingR)).atStack .halt) :=
  ⟨replayBlock blockedActivation.evals.1, replayBlock blockedActivation.evals.2⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Tests
