module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms
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
  | finish (delta : Nat) : Op results results

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .advance, input => .cons (.control 0) input
    | .finish _, input => input

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
  step opcode input store :=
    match opcode, input with
    | .advance, .cons (.control mode) (.cons (.data n) .nil) => action mode n store
    | .finish delta, input => .some (input, 2 * store + delta)

private theorem carry_related (mode : Fin 2) (n : Nat) : TupleRelated machine Eq (carry mode n) (carry mode n) :=
  .cons (.control mode) (.cons (ValueRelated.data (m := machine) (t := ()) n) .nil)

private theorem respects : ActionsRespect primitives Eq := by
  intro _ _ opcode _ _ related store
  cases opcode with
  | finish delta => exact .returned related (2 * store + delta)
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

section DepthThree

private abbrev deepCarry : Ports T := .control 2 :: outerCarry
private abbrev deepFn : Function Unit Unit := ⟨deepCarry, results⟩

private def middleInitial : Wires deepCarry [] outerCarry :=
  .cons (.arg (.tail .head))
    (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))

private def middleOutputs : Wires deepCarry [outerCarry] (Theta.BodyResults deepCarry) :=
  .cons (.arg .head) (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head)
    (.cons (.output (0 : Fin 1) (.tail .head))
      (.cons (.output (0 : Fin 1) (.tail (.tail .head))) .nil))))

private def deepInitial : Wires deepCarry [] deepCarry :=
  .cons (.arg .head) (.cons (.arg (.tail .head))
    (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil)))

private def deepOutputs : Wires deepCarry [deepCarry] results :=
  .cons (.output (0 : Fin 1) (.tail (.tail (.tail .head))))
    (.cons (.arg (.tail (.tail (.tail .head)))) .nil)

private abbrev middleL : Gamma.LoopBody Op deepCarry [outerCarry] := Gamma.loopCode middleInitial innerL middleOutputs
private abbrev middleR : Gamma.LoopBody Op deepCarry [outerCarry] := Gamma.loopCode middleInitial innerR middleOutputs
private abbrev deepL := Gamma.loopCode deepInitial middleL deepOutputs
private abbrev deepR := Gamma.loopCode deepInitial middleR deepOutputs
private def deepMap : Renaming := .region (Equiv.refl _) (fun _ _ => outerMap)

private theorem deepCode : Gamma.CodePair Op deepMap deepL deepR :=
  .loop deepInitial deepOutputs rfl <|
    .loop middleInitial middleOutputs rfl <|
      .loop innerInitial innerOutputs rfl (.acyclic ordered)

private theorem unchangedAddresses {args users : Ports T} {past : List (Ports T)}
    (wires : Wires args past users) :
    wires.addresses.map (Address.rename (renameVertex (Equiv.refl (Fin 1)))) = wires.addresses := by
  induction wires with
  | nil => rfl
  | cons origin _ ih =>
    cases origin <;> simp [Wires.addresses, Origin.address, Address.rename, renameVertex, ih]
    intro equal
    exact equal.symm

private theorem thetaIso {args loopPorts outs : Ports T} {sigsL sigsR : List (Ports T)}
    {left : Gamma.LoopBody Op loopPorts sigsL} {right : Gamma.LoopBody Op loopPorts sigsR}
    (body : NestedTheta.Graph.Isomorphic (Instruction Op) left.toGraph right.toGraph)
    (initial : Wires args [] loopPorts) (suffix : Wires args [loopPorts] outs) :
    NestedTheta.Graph.Isomorphic (Instruction Op)
      (Gamma.loopCode initial left suffix).toGraph (Gamma.loopCode initial right suffix).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) (fun i => Fin.cases rfl (fun j => j.elim0) i)
    (fun i => Fin.cases (unchangedAddresses initial) (fun j => j.elim0) i) (unchangedAddresses suffix) ?_
  intro i
  exact Fin.cases (fun _ => body) (fun j => j.elim0) i

private theorem deepIso : NestedTheta.Graph.Isomorphic (Instruction Op) deepL.toGraph deepR.toGraph :=
  thetaIso (thetaIso innerIso middleInitial middleOutputs) deepInitial deepOutputs

private abbrev DeepLambda := NestedTheta.Term (Instruction Op) deepCarry [] [deepCarry] results

private def deepUnit (body : DeepLambda) : OmegaTerm Op [] [deepFn.port] [[deepFn.port]] :=
  ⟨.bind (.lambda ⟨[], .nil, [deepCarry], body⟩) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def deepCallee (body : DeepLambda) : machine.Val deepFn.port :=
  .closure (.nil : Tuple machine.Val []) body.toGraph

private theorem deepLinks (body : DeepLambda) :
    Links primitives 17 (deepUnit body).toGraph .nil 20 (.linked (.cons (deepCallee body) .nil) 20) :=
  .bind (values := .cons (deepCallee body) .nil) (middle := 20) rfl (.ret _ _ _ _)

private def deepInput (outer inner mode : Fin 2) (n : Nat) : Tuple machine.Val deepCarry :=
  .cons (.control outer) (input inner mode n)

private def deepSource (body : DeepLambda) (args : Tuple machine.Val deepCarry) : Config machine Nat results :=
  ⟨Continuation.start (.call (deepCallee body) args), 20⟩

private theorem deepDispatch (outer inner mode : Fin 2) (n : Nat) :
    Gamma.CallPair primitives Eq deepMap results
      (deepSource deepL (deepInput outer inner mode n)) (deepSource deepR (deepInput outer inner mode n)) := by
  have iso : (deepUnit deepL).toGraph.RenumberedBy (deepUnit deepR).toGraph modulePositions :=
    ⟨fun i => Fin.cases (.lambda ⟨⟨rfl, rfl⟩, deepIso⟩) (fun j => j.elim0) i, rfl⟩
  have schedule : Ordered Op (renameVertex modulePositions) [] [deepFn.port]
      (deepUnit deepL).toGraph.toTerm.region (deepUnit deepR).toGraph.toTerm.region := by
    rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
    exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, deepIso⟩) (.ret _ _)
  let args := deepInput outer inner mode n
  have paired := Gamma.link_then_invoke (mapping := deepMap) respects iso schedule
    (fun i => by simp [renameVertex, modulePositions]) .nil .head
    (.cons (.control outer) (.cons (.control inner) (carry_related mode n))) 20
    (unitL := 17) (unitR := 17) (by
      intro _ _ _ linkedL linkedR _
      cases outcome_unique linkedL (deepLinks deepL)
      cases outcome_unique linkedR (deepLinks deepR)
      exact .closure .nil deepCode)
  change Gamma.DispatchPair primitives Eq (renameVertex modulePositions) deepMap results
    ((request 17 (deepUnit deepL).toGraph .nil .head args 20).start primitives)
    ((request 17 (deepUnit deepR).toGraph .nil .head args 20).start primitives) at paired
  rw [start_linked (request := request 17 (deepUnit deepL).toGraph .nil .head args 20) (deepLinks deepL),
    start_linked (request := request 17 (deepUnit deepR).toGraph .nil .head args 20) (deepLinks deepR)] at paired
  cases paired with
  | invoked calls => exact calls

private theorem openDeep (body : DeepLambda) (args : Tuple machine.Val deepCarry) :
    Job.openClosure machine (deepCallee body) args = .region body args PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term args PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph body)

private theorem deepCallEval {body : DeepLambda} {args : Tuple machine.Val deepCarry}
    {outcome : Continuation.Partial.Outcome machine Nat results}
    (ran : Eval primitives (.region body args PUnit.unit) 20 outcome) :
    Eval primitives (.call (deepCallee body) args) 20 outcome :=
  .call ((openDeep body args).symm ▸ ran)

private theorem deepRoute {sigs : List (Ports T)} {body : Gamma.LoopBody Op deepCarry sigs}
    {args : Tuple machine.Val deepCarry} {target : Feedback.Restart machine Nat}
    {pending : Pending machine target.carried deepCarry}
    (reached : Feedback.Reaches primitives (.iteration body args) 20 target pending) :
    Feedback.Reaches primitives (.call (deepCallee (Gamma.loopCode deepInitial body deepOutputs)) args) 20 target
      (.bind (past := []) (.ret deepOutputs) args PUnit.unit pending) := by
  apply Feedback.Reaches.call
  rw [openDeep]
  have initial : deepInitial.read args PUnit.unit = args := by
    cases args with
    | cons _ tail =>
      cases tail with
      | cons _ tail =>
        cases tail with
        | cons _ tail =>
          cases tail with
          | cons _ tail => cases tail; rfl
  refine .inside (node := Isomorphism.Invocation.loopVertex deepInitial sigs) ?_
  change Feedback.Reaches primitives (.node (.theta deepCarry) (fun _ => sigs) (fun _ => body)
    (deepInitial.read args PUnit.unit)) 20 target pending
  rw [initial]
  exact .theta reached

private theorem middleReturns (outer : Fin 2) (n store : Nat)
    (defined : (bodyOut 0 0 (n + 1), store + 3) ∈ action 0 n store) :
    Eval primitives (.region middleL (deepInput outer 0 0 n) PUnit.unit) store
      (.returned (.cons (.control outer) (deepInput outer 0 0 (n + 1))) (store + 3)) ∧
    Eval primitives (.region middleR (deepInput outer 0 0 n) PUnit.unit) store
      (.returned (.cons (.control outer) (deepInput outer 0 0 (n + 1))) (store + 3)) :=
  let ran := completedInner 0 0 n store defined
  ⟨.bind (node := Isomorphism.Invocation.loopVertex middleInitial [carried])
      (.theta (.stop ran.1 rfl)) (.ret middleOutputs _ _ _),
    .bind (node := Isomorphism.Invocation.loopVertex middleInitial [carried])
      (.theta (.stop ran.2 rfl)) (.ret middleOutputs _ _ _)⟩

private theorem deepExit :
    TerminalPath primitives (deepSource deepL (deepInput 0 0 0 2)) ⟨.returned (output 3 2) .halt, 23⟩ ∧
    TerminalPath primitives (deepSource deepR (deepInput 0 0 0 2)) ⟨.returned (output 3 2) .halt, 23⟩ := by
  have ran := middleReturns 0 2 20 (_root_.Part.mem_some _)
  have left : Eval primitives (.region deepL (deepInput 0 0 0 2) PUnit.unit) 20 (.returned (output 3 2) 23) :=
    .bind (node := Isomorphism.Invocation.loopVertex deepInitial [outerCarry])
      (.theta (.stop ran.1 rfl)) (.ret deepOutputs _ _ _)
  have right : Eval primitives (.region deepR (deepInput 0 0 0 2) PUnit.unit) 20 (.returned (output 3 2) 23) :=
    .bind (node := Isomorphism.Invocation.loopVertex deepInitial [outerCarry])
      (.theta (.stop ran.2 rfl)) (.ret deepOutputs _ _ _)
  exact ⟨⟨(deepCallEval left).steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩,
    ⟨(deepCallEval right).steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩⟩

/-- The third-level call completes one middle restart and then enters
productive innermost feedback, leaving both outer loops pending. -/
private theorem deepInnerCall : InfiniteTrace (Step primitives) (deepSource deepR (deepInput 0 1 1 0)) := by
  apply (deepDispatch 0 1 1 0).infinite_iff.mp
  let args := deepInput 0 1 1 0
  let target : Feedback.Restart machine Nat := ⟨carried, [[], bodyResults], embed left.toTerm, (carry 1 1, 23)⟩
  let savedMiddle : Pending machine carried (Theta.BodyResults deepCarry) :=
    .bind (past := []) (.ret middleOutputs) args PUnit.unit (.loop innerL innerPending)
  have middle : Feedback.Reaches primitives (.region middleL args PUnit.unit) 20 target savedMiddle :=
    .inside (node := Isomorphism.Invocation.loopVertex middleInitial [carried])
      (.theta (.iteration (current := (input 1 1 1, 23)) (.single outerOnce.1) innerEnteredL))
  have outer : Feedback.Reaches primitives (.iteration middleL args) 20 target (.loop middleL savedMiddle) :=
    .iteration (current := (args, 20)) .refl middle
  have run : Feedback.Run primitives (embed left.toTerm) target.input :=
    InfiniteTrace.map (R := FeedbackPair primitives left right) (S := Feedback.Iteration primitives (embed left.toTerm))
      (fun current => (current.left, current.store)) (fun _ _ h => h.1) innerStream
  have productive : Feedback.Productive primitives (.call (deepCallee deepL) args) 20 :=
    ⟨target, _, deepRoute outer, run⟩
  exact productive.infinite .halt

private def deepAt (outer inner mode : Fin 2) (n store : Nat) : Carries machine Eq Nat deepCarry :=
  ⟨deepInput outer inner mode n, deepInput outer inner mode n,
    .cons (.control outer) (.cons (.control inner) (carry_related mode n)), store⟩

private theorem deepOuterStream :
    InfiniteTrace (Gamma.IterationPair primitives middleL middleR) (deepAt 1 0 0 2 20) := by
  refine ⟨fun n => deepAt 1 0 0 (n + 2) (20 + 3 * n), rfl, ?_⟩
  intro n
  have sameStore : 20 + 3 * (n + 1) = 20 + 3 * n + 3 := by omega
  change Gamma.IterationPair primitives middleL middleR (deepAt 1 0 0 (n + 2) (20 + 3 * n))
    (deepAt 1 0 0 ((n + 1) + 2) (20 + 3 * (n + 1)))
  rw [sameStore]
  have defined : (bodyOut 0 0 (n + 2 + 1), 20 + 3 * n + 3) ∈ action 0 (n + 2) (20 + 3 * n) := by
    have notOne : n + 2 ≠ 1 := by omega
    have notZero : n + 2 ≠ 0 := by omega
    unfold action
    rw [ite_eq_right (by decide : ¬ (0 : Fin 2).val = 1), ite_eq_right notOne, ite_eq_right notZero]
    exact _root_.Part.mem_some _
  obtain ⟨ranL, ranR⟩ := middleReturns 1 (n + 2) (20 + 3 * n) defined
  exact ⟨⟨.control 1, ranL, rfl⟩, ⟨.control 1, ranR, rfl⟩⟩

/-- Successive top-level restarts finish both inner levels. Start on
the right linked graph and use the reverse direction of transport. -/
private theorem deepOuterCall : InfiniteTrace (Step primitives) (deepSource deepL (deepInput 1 0 0 2)) := by
  apply (deepDispatch 1 0 0 2).infinite_iff.mpr
  let args := deepInput 1 0 0 2
  let target : Feedback.Restart machine Nat := ⟨deepCarry, [outerCarry], middleR, (args, 20)⟩
  have arrived : Feedback.Reaches primitives (.iteration middleR args) 20 target .empty :=
    .restart (input := target.input) (current := target.input) .refl
  have productive : Feedback.Productive primitives (.call (deepCallee deepR) args) 20 :=
    ⟨target, _, deepRoute arrived, (Gamma.IterationPair.runs deepOuterStream).2⟩
  exact productive.infinite .halt

private def wrapBlock {args loopPorts outs : Ports T} {sigs : List (Ports T)}
    (body : Gamma.LoopBody Op loopPorts sigs) (suffix : Wires args [loopPorts] outs) (entry : Tuple machine.Val args)
    (stop : Gamma.Block machine Nat (Theta.BodyResults loopPorts)) : Gamma.Block machine Nat outs :=
  ⟨stop.site, .bind (past := []) (.ret suffix) entry PUnit.unit (.loop body stop.pending), stop.store⟩

private abbrev middleStopL := wrapBlock innerL middleOutputs (deepInput 0 0 0 0) (stopped left pendingL)
private abbrev middleStopR := wrapBlock innerR middleOutputs (deepInput 0 0 0 0) (stopped right pendingR)
private abbrev deepStopL := wrapBlock middleL deepOutputs (deepInput 0 0 0 0) middleStopL
private abbrev deepStopR := wrapBlock middleR deepOutputs (deepInput 0 0 0 0) middleStopR
private def deepLocation (site : Nat) : Gamma.Location := .loop (.loop (.loop (.acyclic (.here site))))

private theorem deepBlocked :
    Gamma.BlockPair primitives Eq deepMap deepL deepR (deepInput 0 0 0 0) (deepInput 0 0 0 0) 20
      (deepLocation 1) (deepLocation 0) deepStopL deepStopR := by
  have base : Gamma.BlockPair primitives Eq numbering (embed left.toTerm) (embed right.toTerm)
      (carry 0 1) (carry 0 1) 23 (.acyclic (.here 1)) (.acyclic (.here 0))
      ⟨advanceSite 0 1, pendingL, 23⟩ ⟨advanceSite 0 1, pendingR, 23⟩ :=
    .acyclic (.here 1) (.same (carry_related 0 1)) blockedL blockedR
  have inner : Gamma.BlockPair primitives Eq innerMap innerL innerR (input 0 0 0) (input 0 0 0) 20
      (.loop (.acyclic (.here 1))) (.loop (.acyclic (.here 0))) (stopped left pendingL) (stopped right pendingR) :=
    .loop (map := innerMap) (first := atCarry 0 0 20) (current := atCarry 0 1 23) innerInitial innerOutputs rfl rfl rfl
      (.single (feedback 0 0 20 (_root_.Part.mem_some _))) base
  have middle : Gamma.BlockPair primitives Eq outerMap middleL middleR (deepInput 0 0 0 0) (deepInput 0 0 0 0) 20
      (.loop (.loop (.acyclic (.here 1)))) (.loop (.loop (.acyclic (.here 0)))) middleStopL middleStopR :=
    .loop (map := outerMap) (first := outerInput 0 0 0 20) (current := outerInput 0 0 0 20) middleInitial middleOutputs rfl rfl rfl .refl inner
  exact .loop (map := deepMap) (first := deepAt 0 0 0 0 20) (current := deepAt 0 0 0 0 20) deepInitial deepOutputs rfl rfl rfl .refl middle

/-- All three live θ frames and their suffixes survive the relocated
block. Both machine endpoints retain the exact attempted store 23. -/
private theorem deepBlockedCalls :
    TerminalPath primitives (deepSource deepL (deepInput 0 0 0 0)) (deepStopL.outcome.atStack .halt) ∧
    TerminalPath primitives (deepSource deepR (deepInput 0 0 0 0)) (deepStopR.outcome.atStack .halt) := by
  obtain ⟨ranL, ranR⟩ := deepBlocked.evals
  have callL := deepCallEval ranL
  have callR := deepCallEval ranR
  exact ⟨⟨callL.steps .halt, fun _ => (callL.blocks .halt).no_step⟩,
    ⟨callR.steps .halt, fun _ => (callR.blocks .halt).no_step⟩⟩

end DepthThree

section Application

private abbrev calleeFn : Function Unit Unit := ⟨carried, Theta.BodyResults outerCarry⟩
private abbrev callerFn : Function Unit Unit := ⟨carried, results⟩
private abbrev moduleImports : Ports T := [.control 2]
private abbrev callerPorts : Ports T := calleeFn.port :: carried

private def imported : Tuple machine.Val moduleImports := .cons (.control 0) .nil

private def callArguments : Wires callerPorts [] carried :=
  .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)

private def callInputs : Wires callerPorts [] (calleeFn.port :: carried) :=
  .cons (.arg .head) callArguments

private def callSuffix : Wires callerPorts [calleeFn.results] results :=
  .cons (.output (0 : Fin 1) (.tail (.tail (.tail .head))))
    (.cons (.arg (.tail (.tail .head))) .nil)

private abbrev callerCode := Gamma.applicationCode (Op := Op) calleeFn callInputs callSuffix

private def program (callee : Gamma.LoopBody Op outerCarry [carried]) :
    OmegaTerm Op moduleImports [callerFn.port] [[calleeFn.port], [callerFn.port]] :=
  ⟨.bind (.lambda ⟨moduleImports, .cons (.arg .head) .nil, [carried], callee⟩) <|
    .bind (.lambda ⟨[calleeFn.port], .cons (.output (0 : Fin 1) .head) .nil, [calleeFn.results], callerCode⟩) <|
      .ret (.cons (.output (1 : Fin 2) .head) .nil)⟩

private def calleeValue (body : Gamma.LoopBody Op outerCarry [carried]) : machine.Val calleeFn.port :=
  .closure imported body.toGraph

private def callerValue (body : Gamma.LoopBody Op outerCarry [carried]) : machine.Val callerFn.port :=
  .closure (.cons (calleeValue body) .nil) callerCode.toGraph

private def callerInput (body : Gamma.LoopBody Op outerCarry [carried]) (mode : Fin 2) (n : Nat) :
    Tuple machine.Val callerPorts :=
  .cons (calleeValue body) (carry mode n)

private theorem callerLinks (body : Gamma.LoopBody Op outerCarry [carried]) :
    Links primitives 17 (program body).toGraph imported 20 (.linked (.cons (callerValue body) .nil) 20) :=
  .bind (values := .cons (calleeValue body) .nil) (middle := 20) rfl
    (.bind (values := .cons (callerValue body) .nil) (middle := 20) rfl (.ret _ _ _ _))

private abbrev callPositions : Fin 2 ≃ Fin 2 := Equiv.refl _

private def callSource (body : Gamma.LoopBody Op outerCarry [carried]) (mode : Fin 2) (n : Nat) :
    Config machine Nat results :=
  ⟨Continuation.start (.call (callerValue body) (carry mode n)), 20⟩

private theorem applicationDispatch (mode : Fin 2) (n : Nat) :
    Gamma.CallPair primitives Eq innerMap results (callSource innerL mode n) (callSource innerR mode n) := by
  have sameCaller := NestedTheta.Graph.Isomorphic.refl callerCode.toGraph
  have iso : (program innerL).toGraph.RenumberedBy (program innerR).toGraph callPositions :=
    ⟨two (.lambda ⟨⟨rfl, rfl⟩, innerIso⟩) (.lambda ⟨⟨rfl, rfl⟩, sameCaller⟩), rfl⟩
  have schedule : Ordered Op (renameVertex callPositions) moduleImports [callerFn.port]
      (program innerL).toGraph.toTerm.region (program innerR).toGraph.toTerm.region := by
    rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
    exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, innerIso⟩)
      (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, sameCaller⟩) (.ret _ _))
  let req (body : Gamma.LoopBody Op outerCarry [carried]) :=
    request (m := machine) 17 (program body).toGraph imported .head (carry mode n) 20
  have paired : Gamma.DispatchPair primitives Eq (renameVertex callPositions) innerMap results
      ((req innerL).start primitives) ((req innerR).start primitives) :=
    Gamma.link_then_invoke respects iso schedule (fun i => by simp [renameVertex, callPositions])
      (.cons (.control 0) .nil) .head (carry_related mode n) 20 (by
        intro _ _ _ linkedL linkedR _
        cases outcome_unique linkedL (callerLinks innerL)
        cases outcome_unique linkedR (callerLinks innerR)
        exact .application (.cons (.control 0) .nil) innerIso admitted .nil callArguments callSuffix)
  rw [start_linked (request := req innerL) (callerLinks innerL),
    start_linked (request := req innerR) (callerLinks innerR)] at paired
  cases paired with
  | invoked calls => exact calls

private theorem openCallee (body : Gamma.LoopBody Op outerCarry [carried]) (mode : Fin 2) (n : Nat) :
    Job.openClosure machine (calleeValue body) (carry mode n) = .region body (input 0 mode n) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (input 0 mode n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph body)

private theorem openCaller (body : Gamma.LoopBody Op outerCarry [carried]) (mode : Fin 2) (n : Nat) :
    Job.openClosure machine (callerValue body) (carry mode n) = .region callerCode (callerInput body mode n) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (callerInput body mode n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph callerCode)

private theorem callerEntered (body : Gamma.LoopBody Op outerCarry [carried]) (mode : Fin 2) (n : Nat) :
    Step primitives (callSource body mode n) ⟨.eval (.region callerCode (callerInput body mode n) PUnit.unit) .halt, 20⟩ := by
  apply Step.of_next_some
  change _root_.Part.some (Config.mk (.eval (Job.openClosure machine (callerValue body) (carry mode n)) .halt) 20) = _
  rw [openCaller]

/-- The actual dispatch resumes the caller's suffix with the returned
tuple at store 23. The suffix also reads the caller's saved original 2. -/
private theorem returnsThroughCall (body : Gamma.LoopBody Op outerCarry [carried])
    (ran : Eval primitives (.region body (input 0 0 2) PUnit.unit) 20
      (.returned (.cons (.control 0) (input 0 0 3)) 23)) :
    TerminalPath primitives (callSource body 0 2) ⟨.returned (output 3 2) .halt, 23⟩ := by
  have invoked : Eval primitives (.call (calleeValue body) (carry 0 2)) 20
      (.returned (.cons (.control 0) (input 0 0 3)) 23) :=
    .call ((openCallee body 0 2).symm ▸ ran)
  have resumed := Gamma.resume_application (fn := calleeFn) (inputs := callInputs)
    (entry := callerInput body 0 2) callSuffix (.halt : Continuation.Stack machine results results) rfl invoked
  have suffix : Eval primitives (.region (.ret callSuffix) (callerInput body 0 2)
      (Locals.snoc (past := []) PUnit.unit (.cons (.control 0) (input 0 0 3)))) 23 (.returned (output 3 2) 23) :=
    .ret callSuffix _ _ _
  exact ⟨(resumed.head (callerEntered body 0 2)).trans (suffix.steps .halt), fun _ h => _root_.Part.notMem_none _ h⟩

private theorem callerReturns :
    TerminalPath primitives (callSource innerL 0 2) ⟨.returned (output 3 2) .halt, 23⟩ ∧
    TerminalPath primitives (callSource innerR 0 2) ⟨.returned (output 3 2) .halt, 23⟩ :=
  let ran := completedInner 0 0 2 20 (_root_.Part.mem_some _)
  ⟨returnsThroughCall innerL ran.1, returnsThroughCall innerR ran.2⟩

private def callerStop (body : Gamma.LoopBody Op outerCarry [carried])
    (stop : Gamma.Block machine Nat calleeFn.results) : Gamma.Block machine Nat results :=
  ⟨stop.site, .bind (past := []) (.ret callSuffix) (callerInput body 0 0) PUnit.unit stop.pending, stop.store⟩

private theorem callerBlock :
    Gamma.BlockPair primitives Eq innerMap callerCode callerCode (callerInput innerL 0 0) (callerInput innerR 0 0) 20
      (.application (.theta (.here 1))) (.application (.theta (.here 0)))
      (callerStop innerL (stopped left pendingL)) (callerStop innerR (stopped right pendingR)) :=
  .application (fn := calleeFn) (captured := moduleImports) (left := innerL) (right := innerR)
    (captL := imported) (captR := imported) (argsL := carry 0 0) (argsR := carry 0 0)
    callInputs callSuffix rfl rfl blockedActivation

private theorem blocksThroughCall (body : Gamma.LoopBody Op outerCarry [carried]) {stop : Gamma.Block machine Nat results}
    (ran : Eval primitives (.region callerCode (callerInput body 0 0) PUnit.unit) 20 stop.outcome) :
    TerminalPath primitives (callSource body 0 0) (stop.outcome.atStack .halt) := by
  cases stop
  exact ⟨(ran.steps .halt).head (callerEntered body 0 0), fun _ => (ran.blocks .halt).no_step⟩

/-- The callee blocks with its mapped primitive address at store 23.
The caller's original result binding is still pending on both sides. -/
private theorem callerBlocks :
    TerminalPath primitives (callSource innerL 0 0) ((callerStop innerL (stopped left pendingL)).outcome.atStack .halt) ∧
    TerminalPath primitives (callSource innerR 0 0) ((callerStop innerR (stopped right pendingR)).outcome.atStack .halt) :=
  ⟨blocksThroughCall innerL callerBlock.evals.1, blocksThroughCall innerR callerBlock.evals.2⟩

private theorem callInnerRun : Feedback.Run primitives (embed left.toTerm) (carry 1 1, 20) := by
  refine ⟨fun n => (carry 1 (n + 1), 20 + 3 * n), rfl, ?_⟩
  intro n
  have sameStore : 20 + 3 * (n + 1) = 20 + 3 * n + 3 := by omega
  change Feedback.Iteration primitives (embed left.toTerm) (carry 1 (n + 1), 20 + 3 * n)
    (carry 1 ((n + 1) + 1), 20 + 3 * (n + 1))
  rw [sameStore]
  apply (feedback 1 (n + 1) (20 + 3 * n) ?_).1
  have notZero : n + 1 ≠ 0 := by omega
  unfold action
  rw [ite_eq_left (by decide : (1 : Fin 2).val = 1), ite_eq_right notZero]
  exact _root_.Part.mem_some _

/-- An independent stream of successful callee feedback iterations
replays through the actual application, with the caller suffix saved. -/
private theorem callerDiverges : InfiniteTrace (Step primitives) (callSource innerR 1 1) := by
  apply (applicationDispatch 1 1).infinite_iff.mp
  let target : Feedback.Restart machine Nat := ⟨carried, [[], bodyResults], embed left.toTerm, (carry 1 1, 20)⟩
  let calleePending : Pending machine carried calleeFn.results :=
    .bind (past := []) (.ret innerOutputs) (input 0 1 1) PUnit.unit .empty
  let callerPending : Pending machine carried results :=
    .bind (past := []) (.ret callSuffix) (callerInput innerL 1 1) PUnit.unit calleePending
  have inner : Feedback.Reaches primitives (.region innerL (input 0 1 1) PUnit.unit) 20 target calleePending :=
    .inside (node := Isomorphism.Invocation.loopVertex innerInitial [[], bodyResults])
      (.theta (.restart (input := target.input) (current := target.input) .refl))
  have route : Feedback.Reaches primitives (.region callerCode (callerInput innerL 1 1) PUnit.unit) 20
      target callerPending :=
    .inside (node := Gamma.applicationVertex calleeFn callInputs)
      (.apply (fn := calleeFn) (.call ((openCallee innerL 1 1).symm ▸ inner)))
  exact InfiniteTrace.of_steps ((route.steps .halt).head (callerEntered innerL 1 1))
    (callInnerRun.infinite (callerPending.push .halt))

end Application

section RankedCalls

private abbrev layerPorts (callee : Function Unit Unit) : Ports T := callee.port :: carried

private def layerArguments (callee : Function Unit Unit) : Wires (layerPorts callee) [] carried :=
  .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)

private def layerInputs (callee : Function Unit Unit) : Wires (layerPorts callee) [] (callee.port :: carried) :=
  .cons (.arg .head) (layerArguments callee)

private def suffixOutputs {args head : Ports T} : Wires args [head, results] results :=
  .cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil)

private def effectSuffix {args head : Ports T} (delta : Nat) (wires : Wires args [head] results) :
    Term Op args [head] [results] results :=
  .bind ⟨results, .simple (.finish delta), wires, fun i => i.elim0⟩ (fun i => i.elim0) (.ret suffixOutputs)

private theorem finishSchedule {args head : Ports T} (delta : Nat) (wires : Wires args [head] results)
    (same : wires.addresses.map (Address.rename Renaming.identity.vertices) = wires.addresses) :
    Local.Schedule Op .identity (effectSuffix delta wires) (effectSuffix delta wires) :=
  .bind (Shape.simple (Op.finish delta)) wires wires rfl same (fun i => i.elim0) (.ret suffixOutputs suffixOutputs rfl)

private abbrev middleSuffix := effectSuffix 7 callSuffix
private abbrev middleCode := Gamma.applicationThen calleeFn callInputs middleSuffix

private def outerWires : Wires (layerPorts callerFn) [results] results :=
  .cons (.output (0 : Fin 1) .head) (.cons (.arg (.tail (.tail .head))) .nil)

private abbrev outerSuffix := effectSuffix 11 outerWires
private abbrev topCode := Gamma.applicationThen callerFn (layerInputs callerFn) outerSuffix

private def middleValue (body : Gamma.LoopBody Op outerCarry [carried]) : machine.Val callerFn.port :=
  .closure (.cons (calleeValue body) .nil) middleCode.toGraph

private def topValue (body : Gamma.LoopBody Op outerCarry [carried]) : machine.Val callerFn.port :=
  .closure (.cons (middleValue body) .nil) topCode.toGraph

private def chainProgram (body : Gamma.LoopBody Op outerCarry [carried]) :
    OmegaTerm Op moduleImports [callerFn.port] [[calleeFn.port], [callerFn.port], [callerFn.port]] :=
  ⟨.bind (.lambda ⟨moduleImports, .cons (.arg .head) .nil, [carried], body⟩) <|
    .bind (.lambda ⟨[calleeFn.port], .cons (.output (0 : Fin 1) .head) .nil, [calleeFn.results, results], middleCode⟩) <|
    .bind (.lambda ⟨[callerFn.port], .cons (.output (1 : Fin 2) .head) .nil, [results, results], topCode⟩) <|
      .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private theorem chainLinks (body : Gamma.LoopBody Op outerCarry [carried]) :
    Links primitives 17 (chainProgram body).toGraph imported 20 (.linked (.cons (topValue body) .nil) 20) :=
  .bind (values := .cons (calleeValue body) .nil) (middle := 20) rfl
    (.bind (values := .cons (middleValue body) .nil) (middle := 20) rfl
      (.bind (values := .cons (topValue body) .nil) (middle := 20) rfl (.ret _ _ _ _)))

private def chainSource (body : Gamma.LoopBody Op outerCarry [carried]) (mode : Fin 2) (n : Nat) :
    Config machine Nat results :=
  ⟨Continuation.start (.call (topValue body) (carry mode n)), 20⟩

private theorem rankedPlan :
    Gamma.CallPlan machine Eq innerMap 2 (.cons (middleValue innerL) .nil) (.cons (middleValue innerR) .nil)
      topCode topCode :=
  .application
    (.application (.body (.cons (.control 0) .nil) admitted) innerIso .nil callArguments (finishSchedule 7 callSuffix rfl))
    (NestedTheta.Graph.Isomorphic.refl middleCode.toGraph) .nil (layerArguments callerFn) (finishSchedule 11 outerWires rfl)

private theorem rankedDispatch (mode : Fin 2) (n : Nat) :
    Gamma.CallPair primitives Eq innerMap results (chainSource innerL mode n) (chainSource innerR mode n) := by
  have middle := NestedTheta.Graph.Isomorphic.refl middleCode.toGraph
  have top := NestedTheta.Graph.Isomorphic.refl topCode.toGraph
  let positions : Fin 3 ≃ Fin 3 := Equiv.refl _
  have iso : (chainProgram innerL).toGraph.RenumberedBy (chainProgram innerR).toGraph positions :=
    ⟨Fin.cases (.lambda ⟨⟨rfl, rfl⟩, innerIso⟩)
      (two (.lambda ⟨⟨rfl, rfl⟩, middle⟩) (.lambda ⟨⟨rfl, rfl⟩, top⟩)), rfl⟩
  have schedule : Ordered Op (renameVertex positions) moduleImports [callerFn.port]
      (chainProgram innerL).toGraph.toTerm.region (chainProgram innerR).toGraph.toTerm.region := by
    rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
    exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, innerIso⟩)
      (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, middle⟩) (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, top⟩) (.ret _ _)))
  let req (body : Gamma.LoopBody Op outerCarry [carried]) :=
    request (m := machine) 17 (chainProgram body).toGraph imported .head (carry mode n) 20
  have paired : Gamma.DispatchPair primitives Eq (renameVertex positions) innerMap results
      ((req innerL).start primitives) ((req innerR).start primitives) :=
    Gamma.link_then_invoke respects iso schedule (fun i => by simp [renameVertex, positions])
      (.cons (.control 0) .nil) .head (carry_related mode n) 20 (by
        intro _ _ _ linkedL linkedR _
        cases outcome_unique linkedL (chainLinks innerL)
        cases outcome_unique linkedR (chainLinks innerR)
        exact .plan rankedPlan)
  rw [start_linked (request := req innerL) (chainLinks innerL),
    start_linked (request := req innerR) (chainLinks innerR)] at paired
  cases paired with
  | invoked calls => exact calls

private theorem finishEval {args head : Ports T} {wires : Wires args [head] results}
    (delta : Nat) (entry : Tuple machine.Val args) (bound : Tuple machine.Val head) (store : Nat) :
    let locals := Locals.snoc (past := []) PUnit.unit bound
    Eval primitives (.region (embed (effectSuffix delta wires)) entry locals) store
      (.returned (wires.read entry locals) (2 * store + delta)) :=
  let locals := Locals.snoc (past := []) PUnit.unit bound
  let value := wires.read entry locals
  let site : Site machine := ⟨results, results, .finish delta, fun i => i.elim0, fun i => embed (i.elim0), value⟩
  have effect : Eval primitives site.job store (.returned value (2 * store + delta)) :=
    .primitive site (_root_.Part.mem_some _)
  have readResults : ∀ tuple : Tuple machine.Val results, suffixOutputs.read entry (locals.snoc tuple) = tuple := by
    intro tuple
    cases tuple with
    | cons first rest =>
      cases rest with
      | cons second rest => cases rest; rfl
  have resume : Eval primitives (.region (.ret suffixOutputs) entry (locals.snoc value))
      (2 * store + delta) (.returned value (2 * store + delta)) := by
    simpa only [readResults] using Eval.ret (primitives := primitives) suffixOutputs entry
      (locals.snoc value) (2 * store + delta)
  .bind effect resume

private theorem evalLayer {returns : Ports T} {callable : machine.Val (Function.mk carried returns).port}
    {value : Tuple machine.Val returns} {args : Tuple machine.Val carried} {store middle : Nat}
    {final : Continuation.Partial.Outcome machine Nat results}
    (wires : Wires (layerPorts ⟨carried, returns⟩) [returns] results) (delta : Nat)
    (ran : Eval primitives (.call callable args) store (.returned value middle))
    (suffix : Eval primitives (.region (embed (effectSuffix delta wires)) (.cons callable args)
      (Locals.snoc (past := []) PUnit.unit value)) middle final) :
    Eval primitives (.region (Gamma.applicationThen ⟨carried, returns⟩ (layerInputs ⟨carried, returns⟩) (effectSuffix delta wires))
      (.cons callable args) PUnit.unit) store final := by
  let callee : Function Unit Unit := ⟨carried, returns⟩
  have selected : (layerInputs callee).read (.cons callable args) PUnit.unit = .cons callable args := by
    cases args with
    | cons control tail =>
      cases tail with
      | cons number tail => cases tail; rfl
  exact .bind (node := Gamma.applicationVertex callee (layerInputs callee))
    (selected.symm ▸ Eval.apply (fn := callee) (cs := fun _ => []) (children := fun i => i.elim0) ran) suffix

private theorem layerOpen {callee : Function Unit Unit}
    (body : NestedTheta.Term (Instruction Op) (layerPorts callee) [] [callee.results, results] results)
    (callable : machine.Val callee.port) (args : Tuple machine.Val carried) :
    Job.openClosure machine (.closure (.cons callable .nil) body.toGraph) args =
      .region body (.cons callable args) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (.cons callable args) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph body)

/-- The innermost effect changes 20 to 23. The saved middle and top
suffixes run in order, changing 23 to 53 and then to 117. -/
private theorem chainReturns (body : Gamma.LoopBody Op outerCarry [carried])
    (ran : Eval primitives (.region body (input 0 0 2) PUnit.unit) 20
      (.returned (.cons (.control 0) (input 0 0 3)) 23)) :
    TerminalPath primitives (chainSource body 0 2) ⟨.returned (output 3 2) .halt, 117⟩ := by
  have leaf : Eval primitives (.call (calleeValue body) (carry 0 2)) 20
      (.returned (.cons (.control 0) (input 0 0 3)) 23) :=
    .call ((openCallee body 0 2).symm ▸ ran)
  have middle : Eval primitives (.call (middleValue body) (carry 0 2)) 20 (.returned (output 3 2) 53) :=
    .call ((layerOpen middleCode (calleeValue body) (carry 0 2)).symm ▸
      evalLayer callSuffix 7 leaf (finishEval 7 _ _ 23))
  have top : Eval primitives (.call (topValue body) (carry 0 2)) 20 (.returned (output 3 2) 117) :=
    .call ((layerOpen topCode (middleValue body) (carry 0 2)).symm ▸
      evalLayer outerWires 11 middle (finishEval 11 _ _ 53))
  exact ⟨top.steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩

private def middleBlock (body : Gamma.LoopBody Op outerCarry [carried])
    (stop : Gamma.Block machine Nat calleeFn.results) : Gamma.Block machine Nat results :=
  ⟨stop.site, .bind (past := []) (embed middleSuffix) (callerInput body 0 0) PUnit.unit stop.pending, stop.store⟩

private def topBlock (body : Gamma.LoopBody Op outerCarry [carried])
    (stop : Gamma.Block machine Nat results) : Gamma.Block machine Nat results :=
  ⟨stop.site, .bind (past := []) (embed outerSuffix) (.cons (middleValue body) (carry 0 0)) PUnit.unit stop.pending,
    stop.store⟩

private abbrev rankedStopL := topBlock innerL (middleBlock innerL (stopped left pendingL))
private abbrev rankedStopR := topBlock innerR (middleBlock innerR (stopped right pendingR))

/-- The real block after one feedback step keeps both saved call
suffixes and the loop frame, with operand 1 at exact store 23. -/
private theorem rankedBlocked :
    Gamma.BlockPair primitives Eq innerMap topCode topCode
      (.cons (middleValue innerL) (carry 0 0)) (.cons (middleValue innerR) (carry 0 0)) 20
      (.application (.application (.theta (.here 1)))) (.application (.application (.theta (.here 0))))
      rankedStopL rankedStopR := by
  have mid : Gamma.BlockPair primitives Eq innerMap middleCode middleCode
      (callerInput innerL 0 0) (callerInput innerR 0 0) 20
      (.application (.theta (.here 1))) (.application (.theta (.here 0)))
      (middleBlock innerL (stopped left pendingL)) (middleBlock innerR (stopped right pendingR)) :=
    .applicationThen callInputs middleSuffix middleSuffix rfl rfl blockedActivation
  exact .applicationThen (layerInputs callerFn) outerSuffix outerSuffix rfl rfl mid

private theorem chainBlocks (body : Gamma.LoopBody Op outerCarry [carried]) {stop : Gamma.Block machine Nat results}
    (ran : Eval primitives (.region topCode (.cons (middleValue body) (carry 0 0)) PUnit.unit) 20 stop.outcome) :
    TerminalPath primitives (chainSource body 0 0) (stop.outcome.atStack .halt) := by
  cases stop
  have top := Eval.call ((layerOpen topCode (middleValue body) (carry 0 0)).symm ▸ ran)
  exact ⟨top.steps .halt, fun _ => (top.blocks .halt).no_step⟩

private theorem rankedFiniteRegression :
    TerminalPath primitives (chainSource innerL 0 2) ⟨.returned (output 3 2) .halt, 117⟩ ∧
    TerminalPath primitives (chainSource innerR 0 2) ⟨.returned (output 3 2) .halt, 117⟩ ∧
    TerminalPath primitives (chainSource innerL 0 0) (rankedStopL.outcome.atStack .halt) ∧
    TerminalPath primitives (chainSource innerR 0 0) (rankedStopR.outcome.atStack .halt) :=
  let ran := completedInner 0 0 2 20 (_root_.Part.mem_some _)
  ⟨chainReturns innerL ran.1, chainReturns innerR ran.2, chainBlocks innerL rankedBlocked.evals.1,
    chainBlocks innerR rankedBlocked.evals.2⟩

/-- A productive leaf keeps both effectful call suffixes pending.
Use the linked theorem to transport its replay to the relocated body. -/
private theorem rankedProductiveRegression : InfiniteTrace (Step primitives) (chainSource innerR 1 1) := by
  apply (rankedDispatch 1 1).infinite_iff.mp
  let args := carry 1 1
  let target : Feedback.Restart machine Nat := ⟨carried, [[], bodyResults], embed left.toTerm, (args, 20)⟩
  let leafFrame : Pending machine carried calleeFn.results :=
    .bind (past := []) (.ret innerOutputs) (input 0 1 1) PUnit.unit .empty
  let midFrame : Pending machine carried results :=
    .bind (past := []) (embed middleSuffix) (callerInput innerL 1 1) PUnit.unit leafFrame
  let topFrame : Pending machine carried results :=
    .bind (past := []) (embed outerSuffix) (.cons (middleValue innerL) args) PUnit.unit midFrame
  have leaf : Feedback.Reaches primitives (.region innerL (input 0 1 1) PUnit.unit) 20 target leafFrame :=
    .inside (node := Isomorphism.Invocation.loopVertex innerInitial [[], bodyResults])
      (.theta (.restart (input := target.input) (current := target.input) .refl))
  have middle : Feedback.Reaches primitives (.region middleCode (callerInput innerL 1 1) PUnit.unit)
      20 target midFrame :=
    .inside (node := Gamma.applicationVertex calleeFn callInputs)
      (.apply (fn := calleeFn) (.call ((openCallee innerL 1 1).symm ▸ leaf)))
  have top : Feedback.Reaches primitives (.region topCode (.cons (middleValue innerL) args) PUnit.unit)
      20 target topFrame :=
    .inside (node := Gamma.applicationVertex callerFn (layerInputs callerFn))
      (.apply (fn := callerFn) (.call ((layerOpen middleCode (calleeValue innerL) args).symm ▸ middle)))
  have productive : Feedback.Productive primitives (.call (topValue innerL) args) 20 :=
    ⟨target, _, .call ((layerOpen topCode (middleValue innerL) args).symm ▸ top), callInnerRun⟩
  exact productive.infinite .halt

end RankedCalls

section SequentialCalls

private abbrev firstFn : Function Unit Unit := ⟨carried, carried⟩
private abbrev sequenceCaptures : Ports T := [firstFn.port, calleeFn.port]
private abbrev sequenceArgs : Ports T := sequenceCaptures ++ carried

private def firstOutputs : Wires carried [bodyResults] carried :=
  .cons (.output (0 : Fin 1) (.tail .head)) (.cons (.output (0 : Fin 1) (.tail (.tail .head))) .nil)

private abbrev firstCode : NestedTheta.Term (Instruction Op) carried [] [bodyResults] carried :=
  Gamma.bindPrimitive Op.advance initial (.ret firstOutputs)
private abbrev firstValue : machine.Val firstFn.port := .closure .nil firstCode.toGraph

private def sequenceContext (body : Gamma.LoopBody Op outerCarry [carried]) : Tuple machine.Val sequenceCaptures :=
  .cons firstValue (.cons (calleeValue body) .nil)

private def firstArgs : Wires sequenceArgs [] carried :=
  .cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil)

private def secondArgs : Wires sequenceArgs [carried] carried :=
  .cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)

private abbrev firstInputs : Wires sequenceArgs [] (firstFn.port :: carried) :=
  .cons (.arg (Gamma.capturePort (params := carried) (.head : Port sequenceCaptures firstFn.port))) firstArgs

private abbrev secondInputs : Wires sequenceArgs [carried] (calleeFn.port :: carried) :=
  .cons (.arg (Gamma.capturePort (params := carried) (.tail .head : Port sequenceCaptures calleeFn.port))) secondArgs

private def sequenceOutputs : Wires sequenceArgs [carried, calleeFn.results] results :=
  .cons (.output (1 : Fin 2) (.tail (.tail (.tail .head))))
    (.cons (.output (0 : Fin 2) (.tail .head)) .nil)

private abbrev afterFirst : NestedTheta.Term (Instruction Op) sequenceArgs [carried] [calleeFn.results] results :=
  Gamma.bindApplication calleeFn secondInputs (.ret sequenceOutputs)
private abbrev sequenceCode := Gamma.bindApplication firstFn firstInputs afterFirst

private def sequenceMap : Renaming :=
  .region (Equiv.refl _) (fun vertex _ => if vertex = 1 then innerMap else .identity)

private def sequenceLambda (body : Gamma.LoopBody Op outerCarry [carried]) : machine.Val callerFn.port :=
  .closure (sequenceContext body) sequenceCode.toGraph

private def sequenceModule (body : Gamma.LoopBody Op outerCarry [carried]) :
    OmegaTerm Op moduleImports [callerFn.port] [[firstFn.port], [calleeFn.port], [callerFn.port]] :=
  ⟨.bind (.lambda ⟨[], .nil, [bodyResults], firstCode⟩) <|
    .bind (.lambda ⟨moduleImports, .cons (.arg .head) .nil, [carried], body⟩) <|
    .bind (.lambda ⟨sequenceCaptures, .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil),
      [carried, calleeFn.results], sequenceCode⟩) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private theorem sequenceLinks (body : Gamma.LoopBody Op outerCarry [carried]) :
    Links primitives 17 (sequenceModule body).toGraph imported 20 (.linked (.cons (sequenceLambda body) .nil) 20) :=
  .bind (values := .cons firstValue .nil) (middle := 20) rfl
    (.bind (values := .cons (calleeValue body) .nil) (middle := 20) rfl
      (.bind (values := .cons (sequenceLambda body) .nil) (middle := 20) rfl (.ret _ _ _ _)))

private def sequenceSource (body : Gamma.LoopBody Op outerCarry [carried]) (n : Nat) : Config machine Nat results :=
  ⟨Continuation.start (.call (sequenceLambda body) (carry 0 n)), 20⟩

private theorem sequencePlan :
    Gamma.RankedPlan machine Eq 1 sequenceMap (sequenceContext innerL) (sequenceContext innerR)
      sequenceCode sequenceCode := by
  have first : Gamma.RankedPlan machine Eq 0 (sequenceMap.child 0 0)
      (.nil : Tuple machine.Val []) .nil firstCode firstCode :=
    .primitive (context := []) (params := carried) (past := []) Op.advance initial
      (.suffix (context := []) (params := carried) (past := [bodyResults])
        (left := .ret firstOutputs) (right := .ret firstOutputs) (.ret firstOutputs firstOutputs rfl))
  have second : Gamma.RankedPlan machine Eq 0 (sequenceMap.child 1 0) imported imported innerL innerR :=
    .body admitted
  exact .call (context := sequenceCaptures) (params := carried) (fn := firstFn) .head rfl rfl .nil firstArgs
    (by decide) first
    (.call (context := sequenceCaptures) (params := carried) (fn := calleeFn) (.tail .head) rfl rfl
      (.cons (.control 0) .nil) secondArgs (by decide) second
      (.suffix (context := sequenceCaptures) (params := carried) (past := [carried, calleeFn.results])
        (left := .ret sequenceOutputs) (right := .ret sequenceOutputs) (.ret sequenceOutputs sequenceOutputs rfl)))

private theorem sequenceDispatch (n : Nat) :
    Gamma.CallPair primitives Eq sequenceMap results (sequenceSource innerL n) (sequenceSource innerR n) := by
  have first := NestedTheta.Graph.Isomorphic.refl firstCode.toGraph
  have caller := NestedTheta.Graph.Isomorphic.refl sequenceCode.toGraph
  let positions : Fin 3 ≃ Fin 3 := Equiv.refl _
  have iso : (sequenceModule innerL).toGraph.RenumberedBy (sequenceModule innerR).toGraph positions :=
    ⟨Fin.cases (.lambda ⟨⟨rfl, rfl⟩, first⟩)
      (two (.lambda ⟨⟨rfl, rfl⟩, innerIso⟩) (.lambda ⟨⟨rfl, rfl⟩, caller⟩)), rfl⟩
  have schedule : Ordered Op (renameVertex positions) moduleImports [callerFn.port]
      (sequenceModule innerL).toGraph.toTerm.region (sequenceModule innerR).toGraph.toTerm.region := by
    rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
    exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, first⟩)
      (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, innerIso⟩) (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, caller⟩) (.ret _ _)))
  let req (body : Gamma.LoopBody Op outerCarry [carried]) :=
    request (m := machine) 17 (sequenceModule body).toGraph imported .head (carry 0 n) 20
  have paired : Gamma.DispatchPair primitives Eq (renameVertex positions) sequenceMap results
      ((req innerL).start primitives) ((req innerR).start primitives) :=
    Gamma.link_then_invoke respects iso schedule (fun i => by simp [renameVertex, positions])
      (.cons (.control 0) .nil) .head (carry_related 0 n) 20 (by
        intro _ _ _ linkedL linkedR _
        cases outcome_unique linkedL (sequenceLinks innerL)
        cases outcome_unique linkedR (sequenceLinks innerR)
        exact .sequence
          (.cons (.closure .nil first) (.cons (.closure (.cons (.control 0) .nil) innerIso) .nil)) sequencePlan)
  rw [start_linked (request := req innerL) (sequenceLinks innerL),
    start_linked (request := req innerR) (sequenceLinks innerR)] at paired
  cases paired with
  | invoked calls => exact calls

private def sequenceEntry (body : Gamma.LoopBody Op outerCarry [carried]) (n : Nat) : Tuple machine.Val sequenceArgs :=
  prependContext (carry 0 n) (sequenceContext body)

private abbrev firstLocals (n : Nat) : Locals machine.Val [carried] :=
  Locals.snoc (past := []) PUnit.unit (carry 0 n)

private theorem openSequence (body : Gamma.LoopBody Op outerCarry [carried]) (n : Nat) :
    Job.openClosure machine (sequenceLambda body) (carry 0 n) =
      .region sequenceCode (sequenceEntry body n) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (sequenceEntry body n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph sequenceCode)

private theorem firstAction (body : Gamma.LoopBody Op outerCarry [carried]) (n : Nat) (tag : Fin 2)
    (defined : (bodyOut tag 0 (n + 1), 23) ∈ action 0 n 20) :
    Eval primitives (.node (Gamma.applicationVertex firstFn firstInputs).kind
      (fun _ => []) (fun i => i.elim0) (firstInputs.read (sequenceEntry body n) PUnit.unit))
      20 (.returned (carry 0 (n + 1)) 23) := by
  have openFirst : Job.openClosure machine firstValue (carry 0 n) = .region firstCode (carry 0 n) PUnit.unit :=
    congrArg (fun term => Job.region (m := machine) (past := []) term (carry 0 n) PUnit.unit)
      (NestedTheta.Term.toTerm_toGraph firstCode)
  have first : Eval primitives (.region firstCode (carry 0 n) PUnit.unit) 20 (.returned (carry 0 (n + 1)) 23) :=
    .bind (node := Gamma.primitiveVertex Op.advance initial) (.primitive (Gamma.primitiveSite Op.advance _) defined)
      (.ret firstOutputs _ _ _)
  exact .apply (fn := firstFn) (.call (openFirst.symm ▸ first))

/-- Real resumption after the first call binds the tuple read by the second site. -/
private theorem reachesSecond (body : Gamma.LoopBody Op outerCarry [carried]) :
    ReflTransGen (Step primitives) (sequenceSource body 0)
      ⟨.eval (.region afterFirst (sequenceEntry body 0) (firstLocals 1)) .halt, 23⟩ := by
  have entered : Step primitives (sequenceSource body 0)
      ⟨.eval (.region sequenceCode (sequenceEntry body 0) PUnit.unit) .halt, 20⟩ := by
    apply Step.of_next_some
    change _root_.Part.some (Config.mk (.eval (Job.openClosure machine (sequenceLambda body) (carry 0 0)) .halt) 20) = _
    rw [openSequence]
  let frame := Continuation.Stack.resume (past := []) afterFirst (sequenceEntry body 0) PUnit.unit .halt
  have ran := (firstAction body 0 1 (_root_.Part.mem_some _)).steps frame
  exact ((ran.head (.of_next_some rfl)).head entered).tail (.of_next_some rfl)

private theorem sequenceReturn (body : Gamma.LoopBody Op outerCarry [carried])
    (ran : Eval primitives (.region body (input 0 0 3) PUnit.unit) 23
      (.returned (.cons (.control 0) (input 0 0 4)) 26)) :
    TerminalPath primitives (sequenceSource body 2) ⟨.returned (output 4 3) .halt, 26⟩ := by
  have rest : Eval primitives (.region afterFirst (sequenceEntry body 2) (firstLocals 3))
      23 (.returned (output 4 3) 26) :=
    .bind (node := Gamma.applicationVertex calleeFn secondInputs)
      (.apply (fn := calleeFn) (.call ((openCallee body 0 3).symm ▸ ran))) (.ret sequenceOutputs _ _ _)
  have caller : Eval primitives (.region sequenceCode (sequenceEntry body 2) PUnit.unit)
      20 (.returned (output 4 3) 26) :=
    .bind (node := Gamma.applicationVertex firstFn firstInputs) (firstAction body 2 0 (_root_.Part.mem_some _)) rest
  have invoked := Eval.call ((openSequence body 2).symm ▸ caller)
  exact ⟨invoked.steps .halt, fun _ h => _root_.Part.notMem_none _ h⟩

private def secondStop {sigs : List (Ports T)} (body : SingleTheta.Body Op carried sigs)
    (pending : Pending machine bodyResults bodyResults) : Gamma.Block machine Nat calleeFn.results :=
  ⟨advanceSite 0 1, .bind (past := []) (.ret innerOutputs) (input 0 0 1) PUnit.unit
    (.loop (embed body.toTerm) pending), 23⟩

private def sequenceStop (body : Gamma.LoopBody Op outerCarry [carried])
    (stop : Gamma.Block machine Nat calleeFn.results) : Gamma.Block machine Nat results :=
  ⟨stop.site, .bind (.ret sequenceOutputs) (sequenceEntry body 0) (firstLocals 1) stop.pending, stop.store⟩

private theorem sequenceBlock :
    Gamma.BlockPair primitives Eq sequenceMap sequenceCode sequenceCode
      (sequenceEntry innerL 0) (sequenceEntry innerR 0) 20
      (.callSite 1 (.theta (.here 1))) (.callSite 1 (.theta (.here 0)))
      (sequenceStop innerL (secondStop left pendingL)) (sequenceStop innerR (secondStop right pendingR)) := by
  have leaf : Gamma.BlockPair primitives Eq innerMap innerL innerR (input 0 0 1) (input 0 0 1) 23
      (.theta (.here 1)) (.theta (.here 0)) (secondStop left pendingL) (secondStop right pendingR) :=
    .theta (first := atCarry 0 1 23) (current := atCarry 0 1 23) innerInitial innerOutputs
      rfl rfl rfl .refl (.here 1) (.same (carry_related 0 1)) blockedL blockedR
  exact .later (nodeL := Gamma.applicationVertex firstFn firstInputs) (nodeR := Gamma.applicationVertex firstFn firstInputs)
    (firstAction innerL 0 1 (_root_.Part.mem_some _)) (firstAction innerR 0 1 (_root_.Part.mem_some _))
    (.atCall (map := sequenceMap) secondInputs (.ret sequenceOutputs) (.ret sequenceOutputs) rfl rfl leaf)

private theorem sequenceBlockPath (body : Gamma.LoopBody Op outerCarry [carried]) {stop : Gamma.Block machine Nat results}
    (ran : Eval primitives (.region sequenceCode (sequenceEntry body 0) PUnit.unit) 20 stop.outcome) :
    TerminalPath primitives (sequenceSource body 0) (stop.outcome.atStack .halt) := by
  cases stop
  have invoked := Eval.call ((openSequence body 0).symm ▸ ran)
  exact ⟨invoked.steps .halt, fun _ => (invoked.blocks .halt).no_step⟩

/-- Both calls execute in order. The first returns at 23 and supplies the
second's full tuple. At input zero, call site 1 blocks on operand 1 at 23.
At input two, both return and the suffix reads both bound results. -/
private theorem sequentialRegression :
    Gamma.CallPair primitives Eq sequenceMap results (sequenceSource innerL 0) (sequenceSource innerR 0) ∧
    TerminalPath primitives (sequenceSource innerL 0) ((sequenceStop innerL (secondStop left pendingL)).outcome.atStack .halt) ∧
    TerminalPath primitives (sequenceSource innerR 0) ((sequenceStop innerR (secondStop right pendingR)).outcome.atStack .halt) ∧
    Gamma.CallPair primitives Eq sequenceMap results (sequenceSource innerL 2) (sequenceSource innerR 2) ∧
    TerminalPath primitives (sequenceSource innerL 2) ⟨.returned (output 4 3) .halt, 26⟩ ∧
    TerminalPath primitives (sequenceSource innerR 2) ⟨.returned (output 4 3) .halt, 26⟩ :=
  let ran := completedInner 0 0 3 23 (_root_.Part.mem_some _)
  ⟨sequenceDispatch 0, sequenceBlockPath innerL sequenceBlock.evals.1, sequenceBlockPath innerR sequenceBlock.evals.2,
    sequenceDispatch 2, sequenceReturn innerL ran.1, sequenceReturn innerR ran.2⟩

end SequentialCalls

section SelectedArmCall

private abbrev guardedFn : Function Unit Unit := ⟨outerCarry, results⟩
private abbrev guardedCaptures : Ports T := [calleeFn.port]
private abbrev guardedPorts : Ports T := guardedCaptures ++ outerCarry

private def guardedSelector : Origin guardedPorts [] (.control 2) := .arg (.tail .head)

private def captureWiring : Tuple (Port guardedCaptures) guardedCaptures := .cons .head .nil

private def guardedArgs : Wires guardedPorts [] carried :=
  .cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil)

private abbrev guardedInputs : Wires guardedPorts [] (.control 2 :: callerPorts) :=
  Gamma.armInputs guardedSelector captureWiring guardedArgs

private def bypassWires : Wires callerPorts [] results :=
  .cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail .head))) .nil)

private def guardedSigs : Fin 2 → List (Ports T) := Fin.cases [calleeFn.results] (fun _ => [])

private def guardedArms (tag : Fin 2) :
    NestedTheta.Term (Instruction Op) callerPorts [] (guardedSigs tag) results :=
  Fin.cases (motive := fun i => NestedTheta.Term (Instruction Op) callerPorts [] (guardedSigs i) results)
    callerCode (fun _ => .ret bypassWires) tag

private def guardedResultWires : Wires guardedPorts [results] results :=
  .cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)

private abbrev guardedSuffix := effectSuffix 7 guardedResultWires

private abbrev guardedCode := Gamma.bindGamma guardedInputs guardedArms (embed guardedSuffix)

private def callArmMap : Renaming := .region (Equiv.refl _) (fun _ _ => innerMap)
private def guardedMap : Renaming := .region (Equiv.refl _) (fun _ arm => if arm = 0 then callArmMap else .identity)

private def guardedCapture (body : Gamma.LoopBody Op outerCarry [carried]) : Tuple machine.Val guardedCaptures :=
  .cons (calleeValue body) .nil

private def guardedProgram (body : Gamma.LoopBody Op outerCarry [carried]) :
    OmegaTerm Op moduleImports [guardedFn.port] [[calleeFn.port], [guardedFn.port]] :=
  ⟨.bind (.lambda ⟨moduleImports, .cons (.arg .head) .nil, [carried], body⟩) <|
    .bind (.lambda ⟨guardedCaptures, .cons (.output (0 : Fin 1) .head) .nil, [results, results], guardedCode⟩) <|
    .ret (.cons (.output (1 : Fin 2) .head) .nil)⟩

private def guardedLambda (body : Gamma.LoopBody Op outerCarry [carried]) : machine.Val guardedFn.port :=
  .closure (guardedCapture body) guardedCode.toGraph

private theorem guardedLinks (body : Gamma.LoopBody Op outerCarry [carried]) :
    Links primitives 17 (guardedProgram body).toGraph imported 20 (.linked (.cons (guardedLambda body) .nil) 20) :=
  .bind (values := .cons (calleeValue body) .nil) (middle := 20) rfl
    (.bind (values := .cons (guardedLambda body) .nil) (middle := 20) rfl (.ret _ _ _ _))

private def guardedSource (body : Gamma.LoopBody Op outerCarry [carried]) (tag : Fin 2) (n : Nat) :
    Config machine Nat results :=
  ⟨Continuation.start (.call (guardedLambda body) (input tag 0 n)), 20⟩

private theorem guardedPlan :
    Gamma.RankedPlan machine Eq 1 guardedMap (guardedCapture innerL) (guardedCapture innerR) guardedCode guardedCode := by
  have callee : Gamma.RankedPlan machine Eq 0 innerMap imported imported innerL innerR := .body admitted
  have calls : Gamma.RankedPlan machine Eq 1 callArmMap (guardedCapture innerL) (guardedCapture innerR)
      (guardedArms 0) (guardedArms 0) :=
    .call (context := guardedCaptures) (params := carried) (fn := calleeFn) .head rfl rfl
      (.cons (.control 0) .nil) callArguments (by decide) callee
      (.suffix (context := guardedCaptures) (params := carried) (past := [calleeFn.results])
        (left := .ret callSuffix) (right := .ret callSuffix) (.ret callSuffix callSuffix rfl))
  have bypass : Gamma.RankedPlan machine Eq 1 .identity (guardedCapture innerL) (guardedCapture innerR)
      (guardedArms 1) (guardedArms 1) :=
    .suffix (context := guardedCaptures) (params := carried) (past := [])
      (left := .ret bypassWires) (right := .ret bypassWires) (.ret bypassWires bypassWires rfl)
  exact .gamma (context := guardedCaptures) (params := outerCarry) (extra := 0) (past := [])
    guardedSelector captureWiring guardedArgs (two calls bypass)
    (.suffix (context := guardedCaptures) (params := outerCarry) (past := [results])
      (finishSchedule 7 guardedResultWires rfl))

private theorem guardedDispatch (tag : Fin 2) (n : Nat) :
    Gamma.CallPair primitives Eq guardedMap results (guardedSource innerL tag n) (guardedSource innerR tag n) := by
  have caller := NestedTheta.Graph.Isomorphic.refl guardedCode.toGraph
  let positions : Fin 2 ≃ Fin 2 := Equiv.refl _
  have iso : (guardedProgram innerL).toGraph.RenumberedBy (guardedProgram innerR).toGraph positions :=
    ⟨two (.lambda ⟨⟨rfl, rfl⟩, innerIso⟩) (.lambda ⟨⟨rfl, rfl⟩, caller⟩), rfl⟩
  have schedule : Ordered Op (renameVertex positions) moduleImports [guardedFn.port]
      (guardedProgram innerL).toGraph.toTerm.region (guardedProgram innerR).toGraph.toTerm.region := by
    rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
    exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, innerIso⟩) (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, caller⟩) (.ret _ _))
  let req (body : Gamma.LoopBody Op outerCarry [carried]) :=
    request (m := machine) 17 (guardedProgram body).toGraph imported .head (input tag 0 n) 20
  have paired : Gamma.DispatchPair primitives Eq (renameVertex positions) guardedMap results
      ((req innerL).start primitives) ((req innerR).start primitives) :=
    Gamma.link_then_invoke respects iso schedule (fun i => by simp [renameVertex, positions])
      (.cons (.control 0) .nil) .head (.cons (.control tag) (carry_related 0 n)) 20 (by
        intro _ _ _ linkedL linkedR _
        cases outcome_unique linkedL (guardedLinks innerL)
        cases outcome_unique linkedR (guardedLinks innerR)
        exact .sequence (.cons (.closure (.cons (.control 0) .nil) innerIso) .nil) guardedPlan)
  rw [start_linked (request := req innerL) (guardedLinks innerL),
    start_linked (request := req innerR) (guardedLinks innerR)] at paired
  cases paired with
  | invoked calls => exact calls

private def guardedEntry (body : Gamma.LoopBody Op outerCarry [carried]) (tag : Fin 2) (n : Nat) :
    Tuple machine.Val guardedPorts :=
  prependContext (input tag 0 n) (guardedCapture body)

private theorem openGuarded (body : Gamma.LoopBody Op outerCarry [carried]) (tag : Fin 2) (n : Nat) :
    Job.openClosure machine (guardedLambda body) (input tag 0 n) = .region guardedCode (guardedEntry body tag n) PUnit.unit :=
  congrArg (fun code => Job.region (m := machine) (past := []) code (guardedEntry body tag n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph guardedCode)

private theorem guardedReturn (body : Gamma.LoopBody Op outerCarry [carried]) (tag : Fin 2) (n : Nat)
    {value : Tuple machine.Val results} {middle : Nat}
    (ran : Eval primitives (.region (guardedArms tag) (callerInput body 0 n) PUnit.unit) 20 (.returned value middle)) :
    TerminalPath primitives (guardedSource body tag n) ⟨.returned value .halt, 2 * middle + 7⟩ := by
  have resumes := finishEval (wires := guardedResultWires) 7 (guardedEntry body tag n) value middle
  have reads : guardedResultWires.read (guardedEntry body tag n) (Locals.snoc (past := []) PUnit.unit value) = value := by
    cases value with
    | cons first tail =>
      cases tail with
      | cons second tail => cases tail; rfl
  dsimp only at resumes
  rw [reads] at resumes
  have evaluates : Eval primitives (.region guardedCode (guardedEntry body tag n) PUnit.unit) 20
      (.returned value (2 * middle + 7)) :=
    .bind (node := Gamma.vertex guardedInputs guardedSigs) (.gamma (tag := tag) ran) resumes
  have called := Eval.call ((openGuarded body tag n).symm ▸ evaluates)
  exact ⟨called.steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩

private theorem selectedReturns (body : Gamma.LoopBody Op outerCarry [carried])
    (ran : Eval primitives (.region body (input 0 0 2) PUnit.unit) 20
      (.returned (.cons (.control 0) (input 0 0 3)) 23)) :
    TerminalPath primitives (guardedSource body 0 2) ⟨.returned (output 3 2) .halt, 53⟩ :=
  guardedReturn body 0 2 (value := output 3 2) (middle := 23)
    (.bind (node := Gamma.applicationVertex calleeFn callInputs) (value := .cons (.control 0) (input 0 0 3))
      (middle := 23) (.apply (fn := calleeFn) (.call ((openCallee body 0 2).symm ▸ ran))) (.ret callSuffix _ _ _))

private def guardedStop (body : Gamma.LoopBody Op outerCarry [carried])
    (stop : Gamma.Block machine Nat results) : Gamma.Block machine Nat results :=
  ⟨stop.site, .bind (past := []) (embed guardedSuffix) (guardedEntry body 0 0) PUnit.unit stop.pending, stop.store⟩

private theorem guardedBlock :
    Gamma.BlockPair primitives Eq guardedMap guardedCode guardedCode (guardedEntry innerL 0 0) (guardedEntry innerR 0 0)
      20 (.atArm 0 0 (.callSite 0 (.theta (.here 1)))) (.atArm 0 0 (.callSite 0 (.theta (.here 0))))
      (guardedStop innerL (callerStop innerL (stopped left pendingL)))
      (guardedStop innerR (callerStop innerR (stopped right pendingR))) := by
  have inCall : Gamma.BlockPair primitives Eq callArmMap callerCode callerCode
      (callerInput innerL 0 0) (callerInput innerR 0 0) 20
      (.callSite 0 (.theta (.here 1))) (.callSite 0 (.theta (.here 0)))
      (callerStop innerL (stopped left pendingL)) (callerStop innerR (stopped right pendingR)) :=
    .atCall (map := callArmMap) callInputs (.ret callSuffix) (.ret callSuffix) rfl rfl blockedActivation
  exact .atArm (map := guardedMap) (armsL := guardedArms) (armsR := guardedArms) (tag := 0) guardedInputs rfl rfl inCall

private theorem guardedBlockPath (body : Gamma.LoopBody Op outerCarry [carried]) {stop : Gamma.Block machine Nat results}
    (ran : Eval primitives (.region guardedCode (guardedEntry body 0 0) PUnit.unit) 20 stop.outcome) :
    TerminalPath primitives (guardedSource body 0 0) (stop.outcome.atStack .halt) := by
  cases stop
  have called := Eval.call ((openGuarded body 0 0).symm ▸ ran)
  exact ⟨called.steps .halt, fun _ => (called.blocks .halt).no_step⟩

/-- The bypass skips the failing callee and resumes the γ suffix at 20.
The selected returning call resumes it at 23. The selected block retains
both bindings, with operand 1 at relocated primitive address 1 or 0. -/
private theorem selectedArmRegression :
    Gamma.CallPair primitives Eq guardedMap results (guardedSource innerL 0 0) (guardedSource innerR 0 0) ∧
    Gamma.CallPair primitives Eq guardedMap results (guardedSource innerL 1 0) (guardedSource innerR 1 0) ∧
    Gamma.CallPair primitives Eq guardedMap results (guardedSource innerL 0 2) (guardedSource innerR 0 2) ∧
    TerminalPath primitives (guardedSource innerL 1 0) ⟨.returned (output 0 0) .halt, 47⟩ ∧
    TerminalPath primitives (guardedSource innerR 1 0) ⟨.returned (output 0 0) .halt, 47⟩ ∧
    TerminalPath primitives (guardedSource innerL 0 2) ⟨.returned (output 3 2) .halt, 53⟩ ∧
    TerminalPath primitives (guardedSource innerR 0 2) ⟨.returned (output 3 2) .halt, 53⟩ ∧
    TerminalPath primitives (guardedSource innerL 0 0) ((guardedStop innerL (callerStop innerL (stopped left pendingL))).outcome.atStack .halt) ∧
    TerminalPath primitives (guardedSource innerR 0 0) ((guardedStop innerR (callerStop innerR (stopped right pendingR))).outcome.atStack .halt) :=
  let ran := completedInner 0 0 2 20 (_root_.Part.mem_some _)
  ⟨guardedDispatch 0 0, guardedDispatch 1 0, guardedDispatch 0 2,
    guardedReturn innerL 1 0 (.ret bypassWires _ _ _), guardedReturn innerR 1 0 (.ret bypassWires _ _ _),
    selectedReturns innerL ran.1, selectedReturns innerR ran.2,
    guardedBlockPath innerL guardedBlock.evals.1, guardedBlockPath innerR guardedBlock.evals.2⟩

end SelectedArmCall

section RankedThetaCall

private abbrev loopCalleeFn : Function Unit Unit := ⟨carried, bodyResults⟩
private abbrev loopCallerFn : Function Unit Unit := ⟨outerCarry, results⟩
private abbrev loopCaptures : Ports T := [loopCalleeFn.port]
private abbrev rankedCarry : Ports T := loopCaptures ++ outerCarry

private def loopCapturePorts : Tuple (Port loopCaptures) loopCaptures := .cons .head .nil

private def loopArguments : Wires rankedCarry [] outerCarry :=
  .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))

private abbrev rankedInitial : Wires rankedCarry [] rankedCarry :=
  Gamma.captureInputs loopCapturePorts loopArguments

private def loopCallArgs : Wires rankedCarry [] carried :=
  .cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil)

private abbrev loopCallInputs : Wires rankedCarry [] (loopCalleeFn.port :: carried) :=
  .cons (.arg (Gamma.capturePort (params := outerCarry) (.head : Port loopCaptures loopCalleeFn.port))) loopCallArgs

private def flowSelector : Origin rankedCarry [bodyResults] (.control 2) := .arg (.tail .head)

private def nextArguments : Wires rankedCarry [bodyResults] outerCarry :=
  .cons (.output (0 : Fin 1) .head)
    (.cons (.output (0 : Fin 1) (.tail .head)) (.cons (.output (0 : Fin 1) (.tail (.tail .head))) .nil))

private abbrev rankedBodyOutputs : Wires rankedCarry [bodyResults] (Theta.BodyResults rankedCarry) :=
  Gamma.loopOutputs (context := loopCaptures) (params := outerCarry) flowSelector nextArguments

private abbrev rankedBody : Gamma.LoopBody Op rankedCarry [bodyResults] :=
  Gamma.bindApplication loopCalleeFn loopCallInputs (.ret rankedBodyOutputs)

private def rankedExitWires : Wires rankedCarry [rankedCarry] results :=
  .cons (.output (0 : Fin 1) (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil)

private abbrev rankedLoopSuffix := effectSuffix 7 rankedExitWires
private abbrev rankedLoopCode := Gamma.bindTheta rankedInitial rankedBody (embed rankedLoopSuffix)

private def bodyMap : Renaming := .region (Equiv.refl _) (fun _ _ => numbering)
private def rankedLoopMap : Renaming := .region (Equiv.refl _) (fun _ _ => bodyMap)

private abbrev leafL := embed left.toTerm
private abbrev leafR := embed right.toTerm

private def leafValue {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) : machine.Val loopCalleeFn.port :=
  .closure .nil leaf.toGraph

private def loopCaptureValues {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) :
    Tuple machine.Val loopCaptures :=
  .cons (leafValue leaf) .nil

private def rankedLoopValue {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) : machine.Val loopCallerFn.port :=
  .closure (loopCaptureValues leaf) rankedLoopCode.toGraph

private def rankedLoopProgram {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) :
    OmegaTerm Op [] [loopCallerFn.port] [[loopCalleeFn.port], [loopCallerFn.port]] :=
  ⟨.bind (.lambda ⟨[], .nil, sigs, leaf⟩) <|
    .bind (.lambda ⟨loopCaptures, .cons (.output (0 : Fin 1) .head) .nil, [rankedCarry, results], rankedLoopCode⟩) <|
    .ret (.cons (.output (1 : Fin 2) .head) .nil)⟩

private theorem rankedLoopLinks {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) :
    Links primitives 17 (rankedLoopProgram leaf).toGraph .nil 20 (.linked (.cons (rankedLoopValue leaf) .nil) 20) :=
  .bind (values := .cons (leafValue leaf) .nil) (middle := 20) rfl
    (.bind (values := .cons (rankedLoopValue leaf) .nil) (middle := 20) rfl (.ret _ _ _ _))

private def rankedLoopSource {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (n : Nat) :
    Config machine Nat results :=
  ⟨Continuation.start (.call (rankedLoopValue leaf) (input 1 0 n)), 20⟩

private theorem rankedLoopPlan :
    Gamma.RankedPlan machine Eq 1 rankedLoopMap (loopCaptureValues leafL) (loopCaptureValues leafR)
      rankedLoopCode rankedLoopCode := by
  have callee : Gamma.RankedPlan machine Eq 0 numbering (context := []) (params := carried)
      .nil .nil leafL leafR :=
    .body (.acyclic ordered)
  have body : Gamma.RankedPlan machine Eq 1 bodyMap (loopCaptureValues leafL) (loopCaptureValues leafR)
      rankedBody rankedBody :=
    .call (context := loopCaptures) (params := outerCarry) (fn := loopCalleeFn) .head rfl rfl
      .nil loopCallArgs (by decide) callee
      (.suffix (context := loopCaptures) (params := outerCarry) (past := [bodyResults])
        (left := .ret rankedBodyOutputs) (right := .ret rankedBodyOutputs)
        (.ret rankedBodyOutputs rankedBodyOutputs rfl))
  have fixed : Gamma.PreservesLoopCaptures Op loopCaptures outerCarry rankedBody :=
    .bind (.ret flowSelector nextArguments)
  exact .theta (context := loopCaptures) (params := outerCarry) (past := []) loopCapturePorts loopArguments body fixed fixed
    (.suffix (context := loopCaptures) (params := outerCarry) (past := [rankedCarry])
      (finishSchedule 7 rankedExitWires rfl))

private theorem rankedThetaDispatch (n : Nat) :
    Gamma.CallPair primitives Eq rankedLoopMap results (rankedLoopSource leafL n) (rankedLoopSource leafR n) := by
  have caller := NestedTheta.Graph.Isomorphic.refl rankedLoopCode.toGraph
  let positions : Fin 2 ≃ Fin 2 := Equiv.refl _
  have iso : (rankedLoopProgram leafL).toGraph.RenumberedBy (rankedLoopProgram leafR).toGraph positions :=
    ⟨two (.lambda ⟨⟨rfl, rfl⟩, embeddedIso⟩) (.lambda ⟨⟨rfl, rfl⟩, caller⟩), rfl⟩
  have schedule : Ordered Op (renameVertex positions) [] [loopCallerFn.port]
      (rankedLoopProgram leafL).toGraph.toTerm.region (rankedLoopProgram leafR).toGraph.toTerm.region := by
    rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
    exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, embeddedIso⟩) (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, caller⟩) (.ret _ _))
  let req {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) :=
    request (m := machine) 17 (rankedLoopProgram leaf).toGraph .nil .head (input 1 0 n) 20
  have paired : Gamma.DispatchPair primitives Eq (renameVertex positions) rankedLoopMap results
      ((req leafL).start primitives) ((req leafR).start primitives) :=
    Gamma.link_then_invoke respects iso schedule (fun i => by simp [renameVertex, positions])
      .nil .head (.cons (.control 1) (carry_related 0 n)) 20 (by
        intro _ _ _ linkedL linkedR _
        cases outcome_unique linkedL (rankedLoopLinks leafL)
        cases outcome_unique linkedR (rankedLoopLinks leafR)
        exact .sequence (.cons (.closure .nil embeddedIso) .nil) rankedLoopPlan)
  rw [start_linked (request := req leafL) (rankedLoopLinks leafL),
    start_linked (request := req leafR) (rankedLoopLinks leafR)] at paired
  cases paired with
  | invoked calls => exact calls

private def rankedCarryValue {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (selector : Fin 2) (n : Nat) : Tuple machine.Val rankedCarry :=
  prependContext (input selector 0 n) (loopCaptureValues leaf)

private theorem openRankedLoop {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (n : Nat) :
    Job.openClosure machine (rankedLoopValue leaf) (input 1 0 n) =
      .region rankedLoopCode (rankedCarryValue leaf 1 n) PUnit.unit :=
  congrArg (fun code => Job.region (m := machine) (past := []) code (rankedCarryValue leaf 1 n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph rankedLoopCode)

private theorem rankedBodyReturns {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (flag tag : Fin 2) (n store : Nat)
    (ran : Eval primitives (.region leaf (carry 0 n) PUnit.unit) store
      (.returned (bodyOut tag 0 (n + 1)) (store + 3))) :
    Eval primitives (.region rankedBody (rankedCarryValue leaf flag n) PUnit.unit) store
      (.returned (.cons (.control flag) (rankedCarryValue leaf tag (n + 1))) (store + 3)) := by
  have opened : Job.openClosure machine (leafValue leaf) (carry 0 n) = .region leaf (carry 0 n) PUnit.unit :=
    congrArg (fun code => Job.region (m := machine) (past := []) code (carry 0 n) PUnit.unit)
      (NestedTheta.Term.toTerm_toGraph leaf)
  exact .bind (node := Gamma.applicationVertex loopCalleeFn loopCallInputs) (value := bodyOut tag 0 (n + 1))
    (middle := store + 3) (.apply (fn := loopCalleeFn) (.call (opened.symm ▸ ran))) (.ret rankedBodyOutputs _ _ _)

private def secondActivation {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) : Config machine Nat results :=
  (Feedback.Restart.mk rankedCarry [bodyResults] rankedBody (rankedCarryValue leaf 0 3, 23)).config
    (.resume (past := []) (embed rankedLoopSuffix) (rankedCarryValue leaf 1 2) PUnit.unit .halt)

/-- The first successful call restarts the real θ at the returned tuple
and store. The parent suffix remains saved beneath the fresh activation. -/
private theorem rankedThetaRestart {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (first : Eval primitives (.region leaf (carry 0 2) PUnit.unit) 20 (.returned (bodyOut 0 0 3) 23)) :
    ReflTransGen (Step primitives) (rankedLoopSource leaf 2) (secondActivation leaf) := by
  let target : Feedback.Restart machine Nat := ⟨rankedCarry, [bodyResults], rankedBody, (rankedCarryValue leaf 0 3, 23)⟩
  let pending : Pending machine rankedCarry results :=
    .bind (past := []) (embed rankedLoopSuffix) (rankedCarryValue leaf 1 2) PUnit.unit .empty
  have firstIteration : Feedback.Iteration primitives rankedBody (rankedCarryValue leaf 1 2, 20) target.input :=
    ⟨.control 1, rankedBodyReturns leaf 1 0 2 20 first, rfl⟩
  have entered : Feedback.Reaches primitives (.region rankedLoopCode (rankedCarryValue leaf 1 2) PUnit.unit)
      20 target pending :=
    .inside (node := Gamma.thetaVertex rankedInitial [bodyResults])
      (.theta (.restart (current := target.input) (.single firstIteration)))
  have reached : Feedback.Reaches primitives (.call (rankedLoopValue leaf) (input 1 0 2)) 20 target pending :=
    .call ((openRankedLoop leaf 2).symm ▸ entered)
  exact reached.steps .halt

private theorem rankedThetaReturns {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (first : Eval primitives (.region leaf (carry 0 2) PUnit.unit) 20 (.returned (bodyOut 0 0 3) 23))
    (second : Eval primitives (.region leaf (carry 0 3) PUnit.unit) 23 (.returned (bodyOut 0 0 4) 26)) :
    TerminalPath primitives (rankedLoopSource leaf 2) ⟨.returned (output 4 2) .halt, 59⟩ := by
  have loop : Eval primitives (.iteration rankedBody (rankedCarryValue leaf 1 2)) 20
      (.returned (rankedCarryValue leaf 0 4) 26) :=
    .again (rankedBodyReturns leaf 1 0 2 20 first) rfl (.stop (rankedBodyReturns leaf 0 0 3 23 second) rfl)
  have whole : Eval primitives (.region rankedLoopCode (rankedCarryValue leaf 1 2) PUnit.unit) 20
      (.returned (output 4 2) 59) :=
    .bind (node := Gamma.thetaVertex rankedInitial [bodyResults]) (.theta loop)
      (finishEval (wires := rankedExitWires) 7 (rankedCarryValue leaf 1 2) (rankedCarryValue leaf 0 4) 26)
  have called := Eval.call ((openRankedLoop leaf 2).symm ▸ whole)
  exact ⟨called.steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩

private def rankedAt (flag : Fin 2) (n store : Nat) : Carries machine Eq Nat rankedCarry :=
  ⟨rankedCarryValue leafL flag n, rankedCarryValue leafR flag n,
    .cons (.closure .nil embeddedIso) (.cons (.control flag) (carry_related 0 n)), store⟩

private theorem rankedOnce :
    Gamma.IterationPair primitives rankedBody rankedBody (rankedAt 1 0 20) (rankedAt 1 1 23) :=
  ⟨⟨.control 1, rankedBodyReturns leafL 1 1 0 20 (bodyReturnsL 0 0 20 (_root_.Part.mem_some _)), rfl⟩,
    ⟨.control 1, rankedBodyReturns leafR 1 1 0 20 (bodyReturnsR 0 0 20 (_root_.Part.mem_some _)), rfl⟩⟩

private def rankedBodyStop {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (pending : Pending machine bodyResults bodyResults) : Gamma.Block machine Nat (Theta.BodyResults rankedCarry) :=
  ⟨advanceSite 0 1, .bind (past := []) (.ret rankedBodyOutputs) (rankedCarryValue leaf 1 1) PUnit.unit pending, 23⟩

private def rankedLoopStop {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (stop : Gamma.Block machine Nat (Theta.BodyResults rankedCarry)) : Gamma.Block machine Nat results :=
  ⟨stop.site, .bind (past := []) (embed rankedLoopSuffix) (rankedCarryValue leaf 1 0) PUnit.unit
    (.loop rankedBody stop.pending), stop.store⟩

private theorem rankedThetaBlock :
    Gamma.BlockPair primitives Eq rankedLoopMap rankedLoopCode rankedLoopCode
      (rankedCarryValue leafL 1 0) (rankedCarryValue leafR 1 0) 20
      (.atLoop 0 (.callSite 0 (.acyclic (.here 1)))) (.atLoop 0 (.callSite 0 (.acyclic (.here 0))))
      (rankedLoopStop leafL (rankedBodyStop leafL pendingL)) (rankedLoopStop leafR (rankedBodyStop leafR pendingR)) := by
  have leaf : Gamma.BlockPair primitives Eq numbering leafL leafR (carry 0 1) (carry 0 1) 23
      (.acyclic (.here 1)) (.acyclic (.here 0)) ⟨advanceSite 0 1, pendingL, 23⟩ ⟨advanceSite 0 1, pendingR, 23⟩ :=
    .acyclic (.here 1) (.same (carry_related 0 1)) blockedL blockedR
  have inBody : Gamma.BlockPair primitives Eq bodyMap rankedBody rankedBody
      (rankedCarryValue leafL 1 1) (rankedCarryValue leafR 1 1) 23
      (.callSite 0 (.acyclic (.here 1))) (.callSite 0 (.acyclic (.here 0)))
      (rankedBodyStop leafL pendingL) (rankedBodyStop leafR pendingR) :=
    .atCall (map := bodyMap) (fn := loopCalleeFn) (captured := []) (left := leafL) (right := leafR) (captL := .nil) (captR := .nil)
      (argsL := carry 0 1) (argsR := carry 0 1)
      (stopL := ⟨advanceSite 0 1, pendingL, 23⟩) (stopR := ⟨advanceSite 0 1, pendingR, 23⟩)
      loopCallInputs (.ret rankedBodyOutputs) (.ret rankedBodyOutputs) rfl rfl leaf
  exact .atLoop (map := rankedLoopMap) rankedInitial rfl rfl rfl (.single rankedOnce) inBody

private theorem rankedThetaBlockPath {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    {stop : Gamma.Block machine Nat results}
    (ran : Eval primitives (.region rankedLoopCode (rankedCarryValue leaf 1 0) PUnit.unit) 20 stop.outcome) :
    TerminalPath primitives (rankedLoopSource leaf 0) (stop.outcome.atStack .halt) := by
  cases stop
  have called := Eval.call ((openRankedLoop leaf 0).symm ▸ ran)
  exact ⟨called.steps .halt, fun _ => (called.blocks .halt).no_step⟩

/-- On both linked exports the first call feeds the next activation.
The second call either exits through the saved suffix or blocks while
the body call and θ bindings remain live. -/
private theorem rankedThetaRegression :
    Gamma.CallPair primitives Eq rankedLoopMap results (rankedLoopSource leafL 2) (rankedLoopSource leafR 2) ∧
    Gamma.CallPair primitives Eq rankedLoopMap results (rankedLoopSource leafL 0) (rankedLoopSource leafR 0) ∧
    ReflTransGen (Step primitives) (rankedLoopSource leafL 2) (secondActivation leafL) ∧
    ReflTransGen (Step primitives) (rankedLoopSource leafR 2) (secondActivation leafR) ∧
    TerminalPath primitives (rankedLoopSource leafL 2) ⟨.returned (output 4 2) .halt, 59⟩ ∧
    TerminalPath primitives (rankedLoopSource leafR 2) ⟨.returned (output 4 2) .halt, 59⟩ ∧
    TerminalPath primitives (rankedLoopSource leafL 0) ((rankedLoopStop leafL (rankedBodyStop leafL pendingL)).outcome.atStack .halt) ∧
    TerminalPath primitives (rankedLoopSource leafR 0) ((rankedLoopStop leafR (rankedBodyStop leafR pendingR)).outcome.atStack .halt) :=
  ⟨rankedThetaDispatch 2, rankedThetaDispatch 0,
    rankedThetaRestart leafL (bodyReturnsL 0 2 20 (_root_.Part.mem_some _)),
    rankedThetaRestart leafR (bodyReturnsR 0 2 20 (_root_.Part.mem_some _)),
    rankedThetaReturns leafL (bodyReturnsL 0 2 20 (_root_.Part.mem_some _)) (bodyReturnsL 0 3 23 (_root_.Part.mem_some _)),
    rankedThetaReturns leafR (bodyReturnsR 0 2 20 (_root_.Part.mem_some _)) (bodyReturnsR 0 3 23 (_root_.Part.mem_some _)),
    rankedThetaBlockPath leafL rankedThetaBlock.evals.1, rankedThetaBlockPath leafR rankedThetaBlock.evals.2⟩

end RankedThetaCall

section JoinedCallChoice

private abbrev choiceFn : Function Unit Unit := ⟨outerCarry, results⟩
private abbrev choiceCaptures : Ports T := [loopCalleeFn.port, loopCalleeFn.port]
private abbrev choiceEntryPorts : Ports T := choiceCaptures ++ outerCarry

private def firstOperands : Wires carried [] results :=
  .cons (.arg (.tail .head)) (.cons (.arg (.tail .head)) .nil)

private def firstResults : Wires carried [results] bodyResults :=
  .cons (.arg .head) (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))

private abbrev firstChoice : Gamma.LoopBody Op carried [results] :=
  Gamma.bindPrimitive (Op.finish 7) firstOperands (.ret firstResults)

private def choiceSelector : Origin choiceEntryPorts [] (.control 2) := .arg (.tail (.tail .head))

private def choicePorts (tag : Fin 2) : Port choiceCaptures loopCalleeFn.port :=
  Fin.cases .head (fun _ => .tail .head) tag

private def choiceArguments : Wires choiceEntryPorts [[loopCalleeFn.port]] carried :=
  .cons (.arg (.tail (.tail (.tail .head))))
    (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)

private def choiceOutputs : Wires choiceEntryPorts [[loopCalleeFn.port], bodyResults] results :=
  .cons (.output (1 : Fin 2) (.tail (.tail .head)))
    (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)

private abbrev choiceApplication := Gamma.joinedInputs (past := []) loopCalleeFn choiceArguments

private abbrev choiceSuffix : NestedTheta.Term (Instruction Op) choiceEntryPorts [[loopCalleeFn.port], bodyResults] [] results :=
  .ret choiceOutputs

private abbrev afterChoice := Gamma.bindApplication loopCalleeFn choiceApplication choiceSuffix

private abbrev choiceCode :=
  Gamma.chooseApplication (past := []) loopCalleeFn choiceSelector choicePorts choiceArguments choiceSuffix

private abbrev choiceVertex := Gamma.vertex (returned := [loopCalleeFn.port]) (Op := Op)
  (Gamma.chooserInputs choiceSelector) (fun _ => [])

private def choiceMap : Renaming :=
  .region (Equiv.refl _) (fun _ arm => if arm = 1 then numbering else .identity)

private def choiceFamily (tag : Fin 2) : Gamma.CallTarget machine loopCalleeFn :=
  Fin.cases ⟨[], [results], [results], .nil, .nil, firstChoice, firstChoice⟩
    (fun _ => ⟨[], [[], bodyResults], [bodyResults, []], .nil, .nil, leafL, leafR⟩) tag

private def choiceValues {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) :
    Tuple machine.Val choiceCaptures :=
  .cons (leafValue firstChoice) (.cons (leafValue leaf) .nil)

private def choiceClosureFor {sigs callerSigs : List (Ports T)}
    (code : NestedTheta.Term (Instruction Op) choiceEntryPorts [] callerSigs results)
    (leaf : Gamma.LoopBody Op carried sigs) : machine.Val choiceFn.port :=
  .closure (choiceValues leaf) code.toGraph

private def choiceProgramFor {sigs callerSigs : List (Ports T)}
    (code : NestedTheta.Term (Instruction Op) choiceEntryPorts [] callerSigs results)
    (leaf : Gamma.LoopBody Op carried sigs) :
    OmegaTerm Op [] [choiceFn.port] [[loopCalleeFn.port], [loopCalleeFn.port], [choiceFn.port]] :=
  ⟨.bind (.lambda ⟨[], .nil, [results], firstChoice⟩) <|
    .bind (.lambda ⟨[], .nil, sigs, leaf⟩) <|
    .bind (.lambda ⟨choiceCaptures, .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil),
      callerSigs, code⟩) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private theorem choiceLinksFor {sigs callerSigs : List (Ports T)}
    (code : NestedTheta.Term (Instruction Op) choiceEntryPorts [] callerSigs results)
    (leaf : Gamma.LoopBody Op carried sigs) (store : Nat) :
    Links primitives 17 (choiceProgramFor code leaf).toGraph .nil store (.linked (.cons (choiceClosureFor code leaf) .nil) store) :=
  .bind (values := .cons (leafValue firstChoice) .nil) (middle := store) rfl
    (.bind (values := .cons (leafValue leaf) .nil) (middle := store) rfl
      (.bind (values := .cons (choiceClosureFor code leaf) .nil) (middle := store) rfl (.ret _ _ _ _)))

private def choiceSourceFor {sigs callerSigs : List (Ports T)}
    (code : NestedTheta.Term (Instruction Op) choiceEntryPorts [] callerSigs results)
    (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n store : Nat) : Config machine Nat results :=
  ⟨Continuation.start (.call (choiceClosureFor code leaf) (input tag 0 n)), store⟩

private abbrev choiceClosure {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) :=
  choiceClosureFor choiceCode leaf

private abbrev choiceSource {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n : Nat) :=
  choiceSourceFor choiceCode leaf tag n 23

private theorem firstChoicePlan : Gamma.RankedPlan machine Eq 0 .identity (context := []) (params := carried)
    .nil .nil firstChoice firstChoice :=
  .primitive (context := []) (params := carried) (past := []) (Op.finish 7) firstOperands
    (.suffix (context := []) (params := carried) (past := [results]) (left := .ret firstResults)
      (right := .ret firstResults) (.ret firstResults firstResults rfl))

private theorem secondChoicePlan : Gamma.RankedPlan machine Eq 0 numbering (context := []) (params := carried)
    .nil .nil leafL leafR :=
  .body (.acyclic ordered)

private theorem choicePlan :
    Gamma.RankedPlan machine Eq 1 choiceMap (choiceValues leafL) (choiceValues leafR) choiceCode choiceCode :=
  .choose (context := choiceCaptures) (params := outerCarry) (past := []) (fn := loopCalleeFn) (extra := 0)
    choiceSelector choicePorts choiceArguments choiceFamily (fun _ => 0) (two rfl rfl) (two rfl rfl)
    (two .nil .nil) (fun _ => by decide) (two firstChoicePlan secondChoicePlan)
    (.suffix (context := choiceCaptures) (params := outerCarry) (past := [[loopCalleeFn.port], bodyResults])
      (left := .ret choiceOutputs) (right := .ret choiceOutputs) (.ret choiceOutputs choiceOutputs rfl))

private theorem choiceDispatchFor {rank : Nat} {callerSigs : List (Ports T)} (mapping : Renaming)
    (code : NestedTheta.Term (Instruction Op) choiceEntryPorts [] callerSigs results)
    (plan : Gamma.RankedPlan machine Eq rank mapping (choiceValues leafL) (choiceValues leafR) code code)
    (tag : Fin 2) (n store : Nat) :
    Gamma.CallPair primitives Eq mapping results (choiceSourceFor code leafL tag n store)
      (choiceSourceFor code leafR tag n store) := by
  have first := NestedTheta.Graph.Isomorphic.refl firstChoice.toGraph
  have caller := NestedTheta.Graph.Isomorphic.refl code.toGraph
  let positions : Fin 3 ≃ Fin 3 := Equiv.refl _
  have iso : (choiceProgramFor code leafL).toGraph.RenumberedBy (choiceProgramFor code leafR).toGraph positions :=
    ⟨Fin.cases (.lambda ⟨⟨rfl, rfl⟩, first⟩)
      (two (.lambda ⟨⟨rfl, rfl⟩, embeddedIso⟩) (.lambda ⟨⟨rfl, rfl⟩, caller⟩)), rfl⟩
  have schedule : Ordered Op (renameVertex positions) [] [choiceFn.port]
      (choiceProgramFor code leafL).toGraph.toTerm.region (choiceProgramFor code leafR).toGraph.toTerm.region := by
    rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
    exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, first⟩)
      (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, embeddedIso⟩) (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, caller⟩) (.ret _ _)))
  let req {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) :=
    request (m := machine) 17 (choiceProgramFor code leaf).toGraph .nil .head (input tag 0 n) store
  have paired : Gamma.DispatchPair primitives Eq (renameVertex positions) mapping results
      ((req leafL).start primitives) ((req leafR).start primitives) :=
    Gamma.link_then_invoke respects iso schedule (fun i => by simp [renameVertex, positions]) .nil .head
      (.cons (.control tag) (carry_related 0 n)) store (by
        intro _ _ _ linkedL linkedR _
        cases outcome_unique linkedL (choiceLinksFor code leafL store)
        cases outcome_unique linkedR (choiceLinksFor code leafR store)
        exact .sequence (.cons (.closure .nil first) (.cons (.closure .nil embeddedIso) .nil)) plan)
  rw [start_linked (request := req leafL) (choiceLinksFor code leafL store),
    start_linked (request := req leafR) (choiceLinksFor code leafR store)] at paired
  cases paired with
  | invoked calls => exact calls

private theorem choiceDispatch (tag : Fin 2) (n : Nat) :
    Gamma.CallPair primitives Eq choiceMap results (choiceSource leafL tag n) (choiceSource leafR tag n) :=
  choiceDispatchFor choiceMap choiceCode choicePlan tag n 23

private def choiceEntry {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n : Nat) :
    Tuple machine.Val choiceEntryPorts :=
  prependContext (input tag 0 n) (choiceValues leaf)

private def selectedValue {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) :
    machine.Val loopCalleeFn.port :=
  (choiceValues leaf).get (choicePorts tag)

private abbrev selectedLocal {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) :
    Locals machine.Val [[loopCalleeFn.port]] :=
  Locals.snoc (past := []) PUnit.unit (.cons (selectedValue leaf tag) .nil)

private theorem openChoice {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n : Nat) :
    Job.openClosure machine (choiceClosure leaf) (input tag 0 n) = .region choiceCode (choiceEntry leaf tag n) PUnit.unit :=
  congrArg (fun code => Job.region (m := machine) (past := []) code (choiceEntry leaf tag n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph choiceCode)

private theorem chooseEvalAt {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n store : Nat) :
    Eval primitives (.node choiceVertex.kind choiceVertex.childSigs (Gamma.chooserArms choicePorts)
      (choiceVertex.inputs.read (choiceEntry leaf tag n) PUnit.unit)) store
      (.returned (.cons (selectedValue leaf tag) .nil) store) :=
  .gamma (tag := tag) (.ret (past := []) (.cons (.arg (choicePorts tag)) .nil) (choiceValues leaf) PUnit.unit store)

private theorem chooseEval {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n : Nat) :
    Eval primitives (.node choiceVertex.kind choiceVertex.childSigs (Gamma.chooserArms choicePorts)
      (choiceVertex.inputs.read (choiceEntry leaf tag n) PUnit.unit)) 23
      (.returned (.cons (selectedValue leaf tag) .nil) 23) :=
  chooseEvalAt leaf tag n 23

private def dispatchedChoice {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n : Nat) :
    Config machine Nat results :=
  ⟨.eval (.call (selectedValue leaf tag) (carry 0 n))
    (.resume choiceSuffix (choiceEntry leaf tag n) (selectedLocal leaf tag) .halt), 23⟩

/-- The real application dispatch reads the γ output in its bound local. -/
private theorem reachesSelectedCall {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n : Nat) :
    ReflTransGen (Step primitives) (choiceSource leaf tag n) (dispatchedChoice leaf tag n) := by
  have entry : Step primitives (choiceSource leaf tag n) ⟨.eval (.region choiceCode (choiceEntry leaf tag n) PUnit.unit) .halt, 23⟩ := by
    apply Step.of_next_some
    change _root_.Part.some (Config.mk (.eval (Job.openClosure machine (choiceClosure leaf) (input tag 0 n)) .halt) 23) = _
    rw [openChoice]
  let parent := Continuation.Stack.resume (past := []) afterChoice (choiceEntry leaf tag n) PUnit.unit .halt
  have entered : Step primitives ⟨.eval (.region choiceCode (choiceEntry leaf tag n) PUnit.unit) .halt, 23⟩
      ⟨.eval (.node choiceVertex.kind choiceVertex.childSigs (Gamma.chooserArms choicePorts)
        (choiceVertex.inputs.read (choiceEntry leaf tag n) PUnit.unit)) parent, 23⟩ :=
    .of_next_some rfl
  have selected := ((chooseEval leaf tag n).steps parent).head entered
  exact (((selected.head entry).tail (.of_next_some rfl)).tail (.of_next_some rfl)).tail (.of_next_some rfl)

private theorem invokeLeaf {sigs : List (Ports T)} {leaf : Gamma.LoopBody Op carried sigs}
    {n store : Nat} {outcome : Continuation.Partial.Outcome machine Nat bodyResults}
    (body : Eval primitives (.region leaf (carry 0 n) PUnit.unit) store outcome) :
    Eval primitives (.call (leafValue leaf) (carry 0 n)) store outcome := by
  have opened : Job.openClosure machine (leafValue leaf) (carry 0 n) = .region leaf (carry 0 n) PUnit.unit :=
    congrArg (fun code => Job.region (m := machine) (past := []) code (carry 0 n) PUnit.unit)
      (NestedTheta.Term.toTerm_toGraph leaf)
  exact .call (opened.symm ▸ body)

private theorem firstChoiceReturnsAt (n store : Nat) :
    Eval primitives (.region firstChoice (carry 0 n) PUnit.unit) store (.returned (bodyOut 0 0 n) (2 * store + 7)) :=
  .bind (node := Gamma.primitiveVertex (Op.finish 7) firstOperands) (value := output n n) (middle := 2 * store + 7)
    (.primitive (Gamma.primitiveSite (Op.finish 7) (output n n)) (_root_.Part.mem_some _)) (.ret firstResults _ _ _)

private theorem firstChoiceReturns :
    Eval primitives (.region firstChoice (carry 0 2) PUnit.unit) 23 (.returned (bodyOut 0 0 2) 53) :=
  firstChoiceReturnsAt 2 23

private theorem choiceReturns {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (arm tag : Fin 2)
    (outStore value : Nat)
    (called : Eval primitives (.call (selectedValue leaf arm) (carry 0 2)) 23 (.returned (bodyOut tag 0 value) outStore)) :
    TerminalPath primitives (choiceSource leaf arm 2) ⟨.returned (output value 2) .halt, outStore⟩ := by
  have whole : Eval primitives (.region choiceCode (choiceEntry leaf arm 2) PUnit.unit) 23
      (.returned (output value 2) outStore) :=
    .bind (node := choiceVertex) (chooseEval leaf arm 2)
      (.bind (node := Gamma.applicationVertex loopCalleeFn choiceApplication)
        (value := bodyOut tag 0 value) (middle := outStore) (.apply (fn := loopCalleeFn) called) (.ret choiceOutputs _ _ _))
  have executed := Eval.call ((openChoice leaf arm 2).symm ▸ whole)
  exact ⟨executed.steps .halt, fun _ h => _root_.Part.notMem_none _ h⟩

private def choiceStop {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (pending : Pending machine bodyResults bodyResults) : Gamma.Block machine Nat results :=
  ⟨advanceSite 0 1, .bind choiceSuffix (choiceEntry leaf 1 1) (selectedLocal leaf 1) pending, 23⟩

private theorem choiceBlock :
    Gamma.BlockPair primitives Eq choiceMap choiceCode choiceCode (choiceEntry leafL 1 1) (choiceEntry leafR 1 1) 23
      (.chosenCall 1 1 (.acyclic (.here 1))) (.chosenCall 1 1 (.acyclic (.here 0)))
      (choiceStop leafL pendingL) (choiceStop leafR pendingR) := by
  have blocked : Gamma.BlockPair primitives Eq numbering leafL leafR (carry 0 1) (carry 0 1) 23
      (.acyclic (.here 1)) (.acyclic (.here 0)) ⟨advanceSite 0 1, pendingL, 23⟩ ⟨advanceSite 0 1, pendingR, 23⟩ :=
    .acyclic (.here 1) (.same (carry_related 0 1)) blockedL blockedR
  exact .later (nodeL := choiceVertex) (nodeR := choiceVertex) (chooseEval leafL 1 1) (chooseEval leafR 1 1)
    (.atChosenCall (map := choiceMap) (fn := loopCalleeFn) (captured := []) (left := leafL) (right := leafR)
      (captL := .nil) (captR := .nil) (stopL := ⟨advanceSite 0 1, pendingL, 23⟩)
      (stopR := ⟨advanceSite 0 1, pendingR, 23⟩) 1 choiceApplication choiceSuffix choiceSuffix rfl rfl blocked)

private theorem choiceBlockPath {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    {stop : Gamma.Block machine Nat results}
    (ran : Eval primitives (.region choiceCode (choiceEntry leaf 1 1) PUnit.unit) 23 stop.outcome) :
    TerminalPath primitives (choiceSource leaf 1 1) (stop.outcome.atStack .halt) := by
  cases stop
  have called := Eval.call ((openChoice leaf 1 1).symm ▸ ran)
  exact ⟨called.steps .halt, fun _ => (called.blocks .halt).no_step⟩

/-- Both choices run as real calls after the join. The relocated block
keeps the application frame and the joined callable in its saved scope. -/
private theorem joinedChoiceRegression :
    (∀ tag, Gamma.CallPair primitives Eq choiceMap results (choiceSource leafL tag 2) (choiceSource leafR tag 2)) ∧
    (∀ tag, ReflTransGen (Step primitives) (choiceSource leafL tag 2) (dispatchedChoice leafL tag 2)) ∧
    (∀ tag, ReflTransGen (Step primitives) (choiceSource leafR tag 2) (dispatchedChoice leafR tag 2)) ∧
    TerminalPath primitives (choiceSource leafL 0 2) ⟨.returned (output 2 2) .halt, 53⟩ ∧
    TerminalPath primitives (choiceSource leafR 0 2) ⟨.returned (output 2 2) .halt, 53⟩ ∧
    TerminalPath primitives (choiceSource leafL 1 2) ⟨.returned (output 3 2) .halt, 26⟩ ∧
    TerminalPath primitives (choiceSource leafR 1 2) ⟨.returned (output 3 2) .halt, 26⟩ ∧
    Gamma.CallPair primitives Eq choiceMap results (choiceSource leafL 1 1) (choiceSource leafR 1 1) ∧
    TerminalPath primitives (choiceSource leafL 1 1) ((choiceStop leafL pendingL).outcome.atStack .halt) ∧
    TerminalPath primitives (choiceSource leafR 1 1) ((choiceStop leafR pendingR).outcome.atStack .halt) :=
  ⟨fun tag => choiceDispatch tag 2, fun tag => reachesSelectedCall leafL tag 2, fun tag => reachesSelectedCall leafR tag 2,
    choiceReturns leafL 0 0 53 2 (invokeLeaf firstChoiceReturns), choiceReturns leafR 0 0 53 2 (invokeLeaf firstChoiceReturns),
    choiceReturns leafL 1 0 26 3 (invokeLeaf (bodyReturnsL 0 2 23 (_root_.Part.mem_some _))),
    choiceReturns leafR 1 0 26 3 (invokeLeaf (bodyReturnsR 0 2 23 (_root_.Part.mem_some _))), choiceDispatch 1 1,
    choiceBlockPath leafL choiceBlock.evals.1, choiceBlockPath leafR choiceBlock.evals.2⟩

private abbrev chosenPorts : Ports T := [loopCalleeFn.port]
private abbrev beforeCopy : List (Ports T) := [chosenPorts, bodyResults]
private abbrev beforeCall : List (Ports T) := beforeCopy ++ [chosenPorts]
private abbrev afterCall : List (Ports T) := beforeCall ++ [bodyResults]

private def prefixWires : Wires choiceEntryPorts [chosenPorts] carried :=
  choiceArguments

private def passSelector : Origin choiceEntryPorts beforeCopy (.control 2) :=
  .output (1 : Fin 2) .head

private abbrev choiceRoute : Gamma.ChoicePrefix Op choiceEntryPorts loopCalleeFn [chosenPorts] beforeCall
    [bodyResults, chosenPorts] :=
  .primitive Op.advance prefixWires (.forward passSelector .done)

private def delayedArguments : Wires choiceEntryPorts beforeCall carried :=
  .cons (.output (1 : Fin 3) (.tail .head))
    (.cons (.output (1 : Fin 3) (.tail (.tail .head))) .nil)

private abbrev delayedInput := Gamma.joinedInputs (past := beforeCopy) loopCalleeFn delayedArguments

private def suffixWires : Wires choiceEntryPorts afterCall results :=
  .cons (.output (3 : Fin 4) (.tail (.tail .head)))
    (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)

private def delayedOutputs : Wires choiceEntryPorts (afterCall ++ [results]) results :=
  .cons (.output (4 : Fin 5) .head) (.cons (.output (4 : Fin 5) (.tail .head)) .nil)

private abbrev delayedSuffix :=
  Gamma.bindPrimitive (Op.finish 5) suffixWires (.ret delayedOutputs)

private abbrev delayedCode :=
  Gamma.chooseApplicationAfter (past := []) loopCalleeFn choiceSelector choicePorts choiceRoute delayedArguments delayedSuffix

private def delayedMap : Renaming :=
  .region (Equiv.refl _) (fun vertex arm => if vertex = 3 ∧ arm = 1 then numbering else .identity)

private theorem delayedPlan :
    Gamma.RankedPlan machine Eq 1 delayedMap (choiceValues leafL) (choiceValues leafR) delayedCode delayedCode :=
  .chooseAfter (context := choiceCaptures) (params := outerCarry) (past := []) (fn := loopCalleeFn) (extra := 0)
    choiceSelector choicePorts choiceRoute delayedArguments choiceFamily (fun _ => 0) (two rfl rfl) (two rfl rfl)
    (two .nil .nil) (fun _ => by decide) (two firstChoicePlan secondChoicePlan)
    (.primitive (context := choiceCaptures) (params := outerCarry) (past := afterCall) (Op.finish 5) suffixWires
      (.suffix (context := choiceCaptures) (params := outerCarry) (past := afterCall ++ [results])
        (left := .ret delayedOutputs) (right := .ret delayedOutputs) (.ret delayedOutputs delayedOutputs rfl)))

private abbrev delayedSource {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n : Nat) :=
  choiceSourceFor delayedCode leaf tag n 20

private theorem delayedDispatch (tag : Fin 2) (n : Nat) :
    Gamma.CallPair primitives Eq delayedMap results (delayedSource leafL tag n) (delayedSource leafR tag n) :=
  choiceDispatchFor delayedMap delayedCode delayedPlan tag n 20

private theorem openDelayed {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (tag : Fin 2) (n : Nat) :
    Job.openClosure machine (choiceClosureFor delayedCode leaf) (input tag 0 n) =
      .region delayedCode (choiceEntry leaf tag n) PUnit.unit :=
  congrArg (fun code => Job.region (m := machine) (past := []) code (choiceEntry leaf tag n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph delayedCode)

private abbrev prefixVertex := Gamma.primitiveVertex Op.advance prefixWires

private abbrev copyInput : Wires choiceEntryPorts beforeCopy [.control 2, loopCalleeFn.port] :=
  .cons passSelector (.cons (Gamma.extendOrigin (Gamma.joinedOrigin (past := []) loopCalleeFn) bodyResults) .nil)

private abbrev copyVertex := Gamma.vertex (returned := chosenPorts) (Op := Op) copyInput (fun _ => [])

private abbrev copyArms := Gamma.chooserArms (Op := Op) (context := chosenPorts) (fn := loopCalleeFn) (extra := 0) (fun _ => .head)

private abbrev advancedLocals {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (arm flag : Fin 2) (n : Nat) : Locals machine.Val beforeCopy :=
  (selectedLocal leaf arm).snoc (bodyOut flag 0 (n + 1))

private abbrev copiedLocals {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (arm flag : Fin 2) (n : Nat) : Locals machine.Val beforeCall :=
  (advancedLocals leaf arm flag n).snoc (.cons (selectedValue leaf arm) .nil)

private theorem prefixEval {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (arm flag : Fin 2) (n : Nat) (defined : (bodyOut flag 0 (n + 1), 23) ∈ action 0 n 20) :
    Eval primitives (.node prefixVertex.kind prefixVertex.childSigs (fun i => i.elim0)
      (prefixWires.read (choiceEntry leaf arm n) (selectedLocal leaf arm))) 20 (.returned (bodyOut flag 0 (n + 1)) 23) :=
  .primitive (primitives := primitives) (Gamma.primitiveSite Op.advance (carry 0 n)) defined

private theorem copyEval {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (arm flag : Fin 2) (n : Nat) :
    Eval primitives (.node copyVertex.kind copyVertex.childSigs copyArms
      (copyInput.read (choiceEntry leaf arm n) (advancedLocals leaf arm flag n))) 23
      (.returned (.cons (selectedValue leaf arm) .nil) 23) :=
  .gamma (tag := flag) (.ret (past := []) (.cons (.arg .head) .nil) (.cons (selectedValue leaf arm) .nil) PUnit.unit 23)

private theorem delayedReturns {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (arm tag : Fin 2)
    (middle value : Nat)
    (called : Eval primitives (.call (selectedValue leaf arm) (carry 0 3)) 23 (.returned (bodyOut tag 0 value) middle)) :
    TerminalPath primitives (delayedSource leaf arm 2) ⟨.returned (output value 2) .halt, 2 * middle + 5⟩ := by
  have whole : Eval primitives (.region delayedCode (choiceEntry leaf arm 2) PUnit.unit) 20
      (.returned (output value 2) (2 * middle + 5)) :=
    .bind (node := choiceVertex) (chooseEvalAt leaf arm 2 20)
      (.bind (node := prefixVertex) (prefixEval leaf arm 0 2 (_root_.Part.mem_some _))
        (.bind (node := copyVertex) (copyEval leaf arm 0 2)
          (.bind (node := Gamma.applicationVertex loopCalleeFn delayedInput) (.apply (fn := loopCalleeFn) called)
            (.bind (node := Gamma.primitiveVertex (Op.finish 5) suffixWires)
              (.primitive (Gamma.primitiveSite (Op.finish 5) (output value 2)) (_root_.Part.mem_some _))
              (.ret delayedOutputs (choiceEntry leaf arm 2) _ (2 * middle + 5))))))
  have executed := Eval.call ((openDelayed leaf arm 2).symm ▸ whole)
  exact ⟨executed.steps .halt, fun _ h => _root_.Part.notMem_none _ h⟩

private abbrev afterPrefix :=
  Gamma.bindGamma copyInput copyArms (Gamma.bindApplication loopCalleeFn delayedInput delayedSuffix)

private def prefixStop {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) :
    Gamma.Block machine Nat results :=
  ⟨Gamma.primitiveSite Op.advance (carry 0 1), .bind afterPrefix (choiceEntry leaf 1 1) (selectedLocal leaf 1) .empty, 20⟩

private theorem prefixBlock :
    Gamma.BlockPair primitives Eq delayedMap delayedCode delayedCode (choiceEntry leafL 1 1) (choiceEntry leafR 1 1) 20
      (.suffix (.here 1)) (.suffix (.here 1)) (prefixStop leafL) (prefixStop leafR) :=
  .later (nodeL := choiceVertex) (nodeR := choiceVertex) (chooseEvalAt leafL 1 1 20) (chooseEvalAt leafR 1 1 20)
    (.atPrimitive (suffixL := afterPrefix) (suffixR := afterPrefix) Op.advance prefixWires (carry_related 0 1) rfl rfl)

private def delayedStop {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs)
    (pending : Pending machine bodyResults bodyResults) : Gamma.Block machine Nat results :=
  ⟨advanceSite 0 1, .bind delayedSuffix (choiceEntry leaf 1 0) (copiedLocals leaf 1 1 0) pending, 23⟩

private theorem delayedBlock :
    Gamma.BlockPair primitives Eq delayedMap delayedCode delayedCode (choiceEntry leafL 1 0) (choiceEntry leafR 1 0) 20
      (.chosenCall 3 1 (.acyclic (.here 1))) (.chosenCall 3 1 (.acyclic (.here 0)))
      (delayedStop leafL pendingL) (delayedStop leafR pendingR) := by
  have blocked : Gamma.BlockPair primitives Eq numbering leafL leafR (carry 0 1) (carry 0 1) 23
      (.acyclic (.here 1)) (.acyclic (.here 0)) ⟨advanceSite 0 1, pendingL, 23⟩ ⟨advanceSite 0 1, pendingR, 23⟩ :=
    .acyclic (.here 1) (.same (carry_related 0 1)) blockedL blockedR
  exact .later (nodeL := choiceVertex) (nodeR := choiceVertex) (chooseEvalAt leafL 1 0 20) (chooseEvalAt leafR 1 0 20)
    (.later (nodeL := prefixVertex) (nodeR := prefixVertex) (prefixEval leafL 1 1 0 (_root_.Part.mem_some _))
      (prefixEval leafR 1 1 0 (_root_.Part.mem_some _))
      (.later (nodeL := copyVertex) (nodeR := copyVertex) (copyEval leafL 1 1 0) (copyEval leafR 1 1 0)
        (.atChosenCall (map := delayedMap) (fn := loopCalleeFn) (captured := []) (left := leafL) (right := leafR)
          (captL := .nil) (captR := .nil) (stopL := ⟨advanceSite 0 1, pendingL, 23⟩)
          (stopR := ⟨advanceSite 0 1, pendingR, 23⟩) 1 delayedInput delayedSuffix delayedSuffix rfl rfl blocked)))

private theorem delayedBlockPath {sigs : List (Ports T)} (leaf : Gamma.LoopBody Op carried sigs) (n : Nat)
    {stop : Gamma.Block machine Nat results}
    (ran : Eval primitives (.region delayedCode (choiceEntry leaf 1 n) PUnit.unit) 20 stop.outcome) :
    TerminalPath primitives (delayedSource leaf 1 n) (stop.outcome.atStack .halt) := by
  cases stop
  have called := Eval.call ((openDelayed leaf 1 n).symm ▸ ran)
  exact ⟨called.steps .halt, fun _ => (called.blocks .halt).no_step⟩

/-- The two linked choices survive a state update and a forwarding γ.
The suffix runs on both returns. The first block occurs before the
copy and application, while the relocated callee block retains the
saved caller scope and suffix at the updated store. -/
private theorem delayedChoiceRegression :
    (∀ tag n, Gamma.CallPair primitives Eq delayedMap results (delayedSource leafL tag n) (delayedSource leafR tag n)) ∧
    TerminalPath primitives (delayedSource leafL 0 2) ⟨.returned (output 3 2) .halt, 111⟩ ∧
    TerminalPath primitives (delayedSource leafR 0 2) ⟨.returned (output 3 2) .halt, 111⟩ ∧
    TerminalPath primitives (delayedSource leafL 1 2) ⟨.returned (output 4 2) .halt, 57⟩ ∧
    TerminalPath primitives (delayedSource leafR 1 2) ⟨.returned (output 4 2) .halt, 57⟩ ∧
    TerminalPath primitives (delayedSource leafL 1 1) ((prefixStop leafL).outcome.atStack .halt) ∧
    TerminalPath primitives (delayedSource leafR 1 1) ((prefixStop leafR).outcome.atStack .halt) ∧
    TerminalPath primitives (delayedSource leafL 1 0) ((delayedStop leafL pendingL).outcome.atStack .halt) ∧
    TerminalPath primitives (delayedSource leafR 1 0) ((delayedStop leafR pendingR).outcome.atStack .halt) :=
  ⟨delayedDispatch,
    delayedReturns leafL 0 0 53 3 (invokeLeaf (firstChoiceReturnsAt 3 23)),
    delayedReturns leafR 0 0 53 3 (invokeLeaf (firstChoiceReturnsAt 3 23)),
    delayedReturns leafL 1 0 26 4 (invokeLeaf (bodyReturnsL 0 3 23 (_root_.Part.mem_some _))),
    delayedReturns leafR 1 0 26 4 (invokeLeaf (bodyReturnsR 0 3 23 (_root_.Part.mem_some _))),
    delayedBlockPath leafL 1 prefixBlock.evals.1, delayedBlockPath leafR 1 prefixBlock.evals.2,
    delayedBlockPath leafL 0 delayedBlock.evals.1, delayedBlockPath leafR 0 delayedBlock.evals.2⟩

end JoinedCallChoice

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Tests
