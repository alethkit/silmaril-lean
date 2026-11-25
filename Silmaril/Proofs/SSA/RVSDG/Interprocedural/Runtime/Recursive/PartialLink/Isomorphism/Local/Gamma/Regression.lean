module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Tests

open SingleTheta (Body Carries FeedbackPair)

open Continuation.Partial
open Continuation.Descent (Pending)
open Isomorphism.Invocation (request)
open PartialLink.Invocation (start_linked)
open Relation (ReflTransGen TransGen)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev carried : Ports T := [.control 2, num]
private abbrev bodyResults : Ports T := Theta.BodyResults carried
private abbrev params : Ports T := .control 2 :: carried
private abbrev armResults : Ports T := [num]
private abbrev results : Ports T := [num, num]
private abbrev fn : Function Unit Unit := ⟨params, results⟩

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
  if mode.val = 1 then .some (bodyOut 1 mode (n + 1), store + 3)
  else if n = 1 then .none
  else if n = 3 then .some (bodyOut 0 mode (n + store), store + 5)
  else .some (bodyOut 1 mode (n + 1), store + 3)

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
            · exact .returned (.cons (.control 1) (carry_related _ _)) _
            · split
              · exact .undefined
              · split
                · exact .returned (.cons (.control 0) (carry_related _ _)) _
                · exact .returned (.cons (.control 1) (carry_related _ _)) _

private def initial {past : List (Ports T)} : Wires carried past carried :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

private def innerOutputs : Wires carried [carried] armResults :=
  .cons (.output (0 : Fin 1) (.tail .head)) .nil

private def gammaInputs : Wires params [] params :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))

private def outputs : Wires params [armResults] results :=
  .cons (.output (0 : Fin 1) .head) (.cons (.arg (.tail (.tail .head))) .nil)

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
    (SingleTheta.code initial left innerOutputs).toGraph (SingleTheta.code initial right innerOutputs).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) (fun i => Fin.cases rfl (fun j => j.elim0) i)
    (fun i => Fin.cases rfl (fun j => j.elim0) i) rfl ?_
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  intro _
  exact embeddedIso

private def skip : Term Op carried [] [] armResults := .ret (.cons (.arg (.tail .head)) .nil)

private def armSigs : Fin 2 → List (Ports T) := Fin.cases [carried] (fun _ => [])

private def armsL : (i : Fin 2) → NestedTheta.Term (Instruction Op) carried [] (armSigs i) armResults :=
  Fin.cases (SingleTheta.code initial left innerOutputs) (fun _ => embed skip)

private def armsR : (i : Fin 2) → NestedTheta.Term (Instruction Op) carried [] (armSigs i) armResults :=
  Fin.cases (SingleTheta.code initial right innerOutputs) (fun _ => embed skip)

private def gammaL := code gammaInputs armsL outputs
private def gammaR := code gammaInputs armsR outputs

private def thetaMap : Renaming := .region (Equiv.refl _) (fun _ _ => numbering)

private def gammaMap : Renaming := .region (Equiv.refl _) (fun _ tag => if tag = 0 then thetaMap else .identity)

private theorem skipGraph : OrderedGraph .identity skip.toGraph skip.toGraph := by
  refine ⟨.intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) rfl (fun i => i.elim0), ?_⟩
  rw [Term.toTerm_toGraph]
  exact .ret _ _ rfl

private theorem pairedCode : CodePair Op gammaMap gammaL gammaR := by
  apply CodePair.gamma gammaInputs outputs rfl
  apply two
  · exact .theta initial innerOutputs rfl ordered
  · have pair := CodePair.acyclic skipGraph
    rw [Term.toTerm_toGraph] at pair
    exact pair

private theorem skipIso : NestedTheta.Graph.Isomorphic (Instruction Op) (embed skip).toGraph (embed skip).toGraph :=
  .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0) rfl (fun i => i.elim0)

private theorem gammaIso : NestedTheta.Graph.Isomorphic (Instruction Op) gammaL.toGraph gammaR.toGraph := by
  refine .intro rfl rfl (Equiv.refl _) (fun i => Fin.cases rfl (fun j => j.elim0) i)
    (fun i => Fin.cases rfl (fun j => j.elim0) i) rfl ?_
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  exact two innerIso skipIso

private def omega (body : NestedTheta.Term (Instruction Op) params [] [armResults] results) :
    OmegaTerm Op [] [fn.port] [[fn.port]] :=
  ⟨.bind (.lambda ⟨[], .nil, [armResults], body⟩) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def modulePositions : Fin 1 ≃ Fin 1 := Equiv.refl _

private theorem moduleIso : (omega gammaL).toGraph.RenumberedBy (omega gammaR).toGraph modulePositions :=
  ⟨fun i => Fin.cases (.lambda ⟨⟨rfl, rfl⟩, gammaIso⟩) (fun j => j.elim0) i, rfl⟩

private theorem moduleSchedule : Ordered Op (renameVertex modulePositions) [] [fn.port]
    (omega gammaL).toGraph.toTerm.region (omega gammaR).toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, gammaIso⟩) (.ret _ _)

private abbrev LambdaBody := NestedTheta.Term (Instruction Op) params [] [armResults] results

private def callable (body : LambdaBody) : machine.Val fn.port :=
  .closure (.nil : Tuple machine.Val []) body.toGraph

private theorem linked (body : LambdaBody) :
    Links primitives 17 (omega body).toGraph .nil 20 (.linked (.cons (callable body) .nil) 20) :=
  .bind (values := .cons (callable body) .nil) (middle := 20) rfl (.ret _ _ _ _)

private def input (branch mode : Fin 2) (n : Nat) : Tuple machine.Val params := .cons (.control branch) (carry mode n)

private abbrev entry (body : LambdaBody) (branch mode : Fin 2) (n : Nat) :=
  request (m := machine) 17 (omega body).toGraph .nil .head (input branch mode n) 20

private def source (body : LambdaBody) (branch mode : Fin 2) (n : Nat) : Config machine Nat results :=
  ⟨Continuation.start (.call (callable body) (input branch mode n)), 20⟩

private theorem started (body : LambdaBody) (branch mode : Fin 2) (n : Nat) :
    (entry body branch mode n).start primitives = .ok (source body branch mode n) :=
  start_linked (request := entry body branch mode n) (linked body)

private theorem dispatch (branch mode : Fin 2) (n : Nat) :
    CallPair primitives Eq gammaMap results (source gammaL branch mode n) (source gammaR branch mode n) := by
  have paired := link_then_invoke (mapping := gammaMap) respects moduleIso moduleSchedule
    (fun i => by simp [renameVertex, modulePositions]) .nil .head (.cons (.control branch) (carry_related mode n)) 20
    (unitL := 17) (unitR := 17) (by
      intro exportsL exportsR post linkedL linkedR _
      cases outcome_unique linkedL (linked gammaL)
      cases outcome_unique linkedR (linked gammaR)
      exact .closure .nil pairedCode)
  change DispatchPair primitives Eq (renameVertex modulePositions) gammaMap results
    ((entry gammaL branch mode n).start primitives) ((entry gammaR branch mode n).start primitives) at paired
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

private theorem leftProductive : Feedback.Run primitives (embed left.toTerm) (carry 1 0, 20) := by
  refine ⟨fun n => (carry 1 n, 20 + 3 * n), rfl, ?_⟩
  intro n
  have update : 20 + 3 * (n + 1) = 20 + 3 * n + 3 := by omega
  change Feedback.Iteration primitives (embed left.toTerm) (carry 1 n, 20 + 3 * n)
    (carry 1 (n + 1), 20 + 3 * (n + 1))
  rw [update]
  exact (feedback 1 n (20 + 3 * n) (_root_.Part.mem_some _)).1


private theorem openFixture (body : LambdaBody) (branch mode : Fin 2) (n : Nat) :
    Job.openClosure machine (callable body) (input branch mode n) =
      .region body (input branch mode n) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (input branch mode n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph body)

private def parent : Continuation.Stack machine carried results :=
  .resume (past := []) (.ret innerOutputs) (carry 1 0) PUnit.unit
    (.resume (past := []) (.ret outputs) (input 0 1 0) PUnit.unit .halt)

private def restartL (n store : Nat) : Config machine Nat results :=
  (Feedback.Restart.mk carried [[], bodyResults] (embed left.toTerm) (carry 1 n, store)).config parent

private def restartR (n store : Nat) : Config machine Nat results :=
  (Feedback.Restart.mk carried [bodyResults, []] (embed right.toTerm) (carry 1 n, store)).config parent

/-- Both saved suffixes remain live as the bodies restart at data 1
and store 23, with a positive segment through each actual body. -/
private theorem firstRestart :
    TransGen (Step primitives) (restartL 0 20) (restartL 1 23) ∧
    TransGen (Step primitives) (restartR 0 20) (restartR 1 23) :=
  let one := feedback 1 0 20 (_root_.Part.mem_some _)
  ⟨one.1.steps parent, one.2.steps parent⟩

private theorem divergentCall : InfiniteTrace (Step primitives) (source gammaR 0 1 0) := by
  apply (dispatch 0 1 0).infinite_iff.mp
  let target : Feedback.Restart machine Nat := ⟨carried, [[], bodyResults], embed left.toTerm, (carry 1 0, 20)⟩
  let inner : Pending machine carried armResults :=
    .bind (past := []) (.ret innerOutputs) (carry 1 0) PUnit.unit .empty
  let frames : Pending machine carried results :=
    .bind (past := []) (.ret outputs) (input 0 1 0) PUnit.unit inner
  have reached : Feedback.Reaches primitives (.region (armsL 0) (carry 1 0) PUnit.unit) 20 target inner :=
    .inside (node := Isomorphism.Invocation.loopVertex initial [[], bodyResults])
      (.theta (.restart (input := target.input) (current := target.input) .refl))
  have route : Feedback.Reaches primitives (.region gammaL (input 0 1 0) PUnit.unit) 20 target frames :=
    .inside (node := vertex gammaInputs armSigs) (.gamma (tag := 0) reached)
  rw [← openFixture gammaL 0 1 0] at route
  have productive : Feedback.Productive primitives (.call (callable gammaL) (input 0 1 0)) 20 :=
    ⟨target, frames, .call route, leftProductive⟩
  exact productive.infinite .halt

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
    Local.BlockAt primitives right.toTerm (carry 0 1) PUnit.unit 23 (numbering.location (.here 1))
      (.blocked (advanceSite 0 1) pendingR 23) := by
  rw [Term.toTerm_toGraph]
  exact Local.BlockAt.here (past := []) Op.advance initial (carry 0 1) PUnit.unit 23 rfl

private def innerStop {sigs : List (Ports T)} (body : Body Op carried sigs)
    (pending : Pending machine bodyResults bodyResults) : Block machine Nat armResults :=
  ⟨advanceSite 0 1, .bind (past := []) (.ret innerOutputs) (carry 0 0) PUnit.unit
    (.loop (embed body.toTerm) pending), 23⟩

private def stopped {sigs : List (Ports T)} (body : Body Op carried sigs)
    (pending : Pending machine bodyResults bodyResults) : Block machine Nat results :=
  let child := innerStop body pending
  ⟨child.site, .bind (past := []) (.ret outputs) (input 0 0 0) PUnit.unit child.pending, child.store⟩

private def blockAddress : Location := .gamma 0 (.theta (.here 1))

/-- After one feedback, the selected arm blocks at the relocated effect.
The diagnostic keeps the live θ and enclosing γ suffix frames. -/
private theorem blockPair :
    BlockPair primitives Eq gammaMap gammaL gammaR (input 0 0 0) (input 0 0 0) 20
      blockAddress (.gamma 0 (.theta (.here 0))) (stopped left pendingL) (stopped right pendingR) := by
  refine BlockPair.gamma (armsL := armsL) (armsR := armsR) (tag := 0)
    (stopL := innerStop left pendingL) (stopR := innerStop right pendingR)
    (entryL := input 0 0 0) (entryR := input 0 0 0) gammaInputs outputs rfl rfl ?_
  exact .theta (first := atCarry 0 0 20) (current := atCarry 0 1 23) initial innerOutputs rfl rfl rfl
    (.single (feedback 0 0 20 (_root_.Part.mem_some _))) (.here 1) (.same (carry_related 0 1)) blockedL blockedR

private theorem evalCall {body : LambdaBody} {branch mode : Fin 2} {n : Nat}
    {outcome : Continuation.Partial.Outcome machine Nat results}
    (ran : Eval primitives (.region body (input branch mode n) PUnit.unit) 20 outcome) :
    Eval primitives (.call (callable body) (input branch mode n)) 20 outcome :=
  .call ((openFixture body branch mode n).symm ▸ ran)

private theorem terminalBlock {body : LambdaBody} {stop : Block machine Nat results}
    (ran : Eval primitives (.region body (input 0 0 0) PUnit.unit) 20 stop.outcome) :
    TerminalPath primitives (source body 0 0 0) (stop.outcome.atStack .halt) := by
  have call := evalCall ran
  exact ⟨call.steps .halt, fun _ => (call.blocks .halt).no_step⟩

private theorem blockedCalls :
    TerminalPath primitives (source gammaL 0 0 0) ((stopped left pendingL).outcome.atStack .halt) ∧
    TerminalPath primitives (source gammaR 0 0 0) ((stopped right pendingR).outcome.atStack .halt) :=
  ⟨terminalBlock blockPair.evals.1, terminalBlock blockPair.evals.2⟩

private def armValue (n : Nat) : Tuple machine.Val armResults := .cons (.data n) .nil

private theorem resumeGamma {arms : (tag : Fin 2) → NestedTheta.Term (Instruction Op) carried [] (armSigs tag) armResults}
    {branch mode : Fin 2} {n value store : Nat}
    (ran : Eval primitives (.region (arms branch) (carry mode n) PUnit.unit) 20 (.returned (armValue value) store)) :
    TerminalPath primitives (source (code gammaInputs arms outputs) branch mode n)
      ⟨.returned (output value n) .halt, store⟩ := by
  have body : Eval primitives (.region (code gammaInputs arms outputs) (input branch mode n) PUnit.unit)
      20 (.returned (output value n) store) :=
    .bind (node := vertex gammaInputs armSigs) (Eval.gamma (cs := armSigs) (children := arms) ran)
      (.ret outputs _ _ _)
  have call := evalCall body
  exact ⟨call.steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩

private theorem exits :
    SingleTheta.Finishes primitives numbering left right (atCarry 0 2 20)
      (.returned (carry 0 26) 28) (.returned (carry 0 26) 28) :=
  ⟨atCarry 0 3 23, .single (feedback 0 2 20 (_root_.Part.mem_some _)),
    .exited (tag := .control 0) rfl (carry_related 0 26)
      (bodyReturnsL 0 3 23 (_root_.Part.mem_some _)) (bodyReturnsR 0 3 23 (_root_.Part.mem_some _))⟩

/-- Both selected arms exit after feedback. The θ result resumes the
enclosing γ suffix, which also reads the original λ argument. -/
private theorem returnedCalls :
    TerminalPath primitives (source gammaL 0 0 2) ⟨.returned (output 26 2) .halt, 28⟩ ∧
    TerminalPath primitives (source gammaR 0 0 2) ⟨.returned (output 26 2) .halt, 28⟩ := by
  constructor
  · apply resumeGamma (arms := armsL)
    exact .bind (node := Isomorphism.Invocation.loopVertex initial [[], bodyResults]) (.theta exits.eval.1)
      (.ret innerOutputs _ _ _)
  · apply resumeGamma (arms := armsR)
    exact .bind (node := Isomorphism.Invocation.loopVertex initial [bodyResults, []]) (.theta exits.eval.2)
      (.ret innerOutputs _ _ _)

/-- With input data 1 the loop's primitive is undefined at entry, yet
selecting arm 1 returns at the original store without attempting it. -/
private theorem skippedLoop :
    action 0 1 20 = _root_.Part.none ∧
    TerminalPath primitives (source gammaL 1 0 1) ⟨.returned (output 1 1) .halt, 20⟩ ∧
    TerminalPath primitives (source gammaR 1 0 1) ⟨.returned (output 1 1) .halt, 20⟩ := by
  refine ⟨rfl, ?_, ?_⟩
  · apply resumeGamma (arms := armsL)
    exact Eval.ret (past := []) (.cons (.arg (.tail .head)) .nil) (carry 0 1) PUnit.unit 20
  · apply resumeGamma (arms := armsR)
    exact Eval.ret (past := []) (.cons (.arg (.tail .head)) .nil) (carry 0 1) PUnit.unit 20

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Tests
