module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Tests

open Continuation.Partial
open Continuation.Descent (Pending)
open Isomorphism.Invocation (request)
open PartialLink.Invocation (start_linked)
open Relation (ReflTransGen TransGen)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev carried : Ports T := [.control 2, num]
private abbrev bodyResults : Ports T := Theta.BodyResults carried
private abbrev results : Ports T := [num, num]
private abbrev fn : Function Unit Unit := ⟨carried, results⟩

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

private def outputs : Wires carried [carried] results :=
  .cons (.output (0 : Fin 1) (.tail .head)) (.cons (.arg (.tail .head)) .nil)

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

private theorem codeIso : NestedTheta.Graph.Isomorphic (Instruction Op)
    (code initial left outputs).toGraph (code initial right outputs).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) (fun i => Fin.cases rfl (fun j => j.elim0) i)
    (fun i => Fin.cases rfl (fun j => j.elim0) i) rfl ?_
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  intro _
  exact embeddedIso

private def lambda {sigs : List (Ports T)} (body : Body Op carried sigs) : LambdaTerm Op [] [] fn :=
  ⟨[], .nil, [carried], code initial body outputs⟩

private def omega {sigs : List (Ports T)} (body : Body Op carried sigs) : OmegaTerm Op [] [fn.port] [[fn.port]] :=
  ⟨.bind (.lambda (lambda body)) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def modulePositions : Fin 1 ≃ Fin 1 := Equiv.refl _

private theorem moduleIso : (omega left).toGraph.RenumberedBy (omega right).toGraph modulePositions :=
  ⟨fun i => Fin.cases (.lambda ⟨⟨rfl, rfl⟩, codeIso⟩) (fun j => j.elim0) i, rfl⟩

private theorem moduleSchedule : Ordered Op (renameVertex modulePositions) [] [fn.port]
    (omega left).toGraph.toTerm.region (omega right).toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .bind rfl (.lambda ⟨⟨rfl, rfl⟩, codeIso⟩) (.ret _ _)

private def callable {sigs : List (Ports T)} (body : Body Op carried sigs) : machine.Val fn.port :=
  .closure (.nil : Tuple machine.Val []) (code initial body outputs).toGraph

private theorem linked {sigs : List (Ports T)} (body : Body Op carried sigs) :
    Links primitives 17 (omega body).toGraph .nil 20 (.linked (.cons (callable body) .nil) 20) :=
  .bind (values := .cons (callable body) .nil) (middle := 20) rfl (.ret _ _ _ _)

private abbrev entry {sigs : List (Ports T)} (body : Body Op carried sigs) (mode : Fin 2) (n : Nat) :=
  request (m := machine) 17 (omega body).toGraph .nil .head (carry mode n) 20

private def source {sigs : List (Ports T)} (body : Body Op carried sigs) (mode : Fin 2) (n : Nat) :
    Config machine Nat results :=
  ⟨Continuation.start (.call (callable body) (carry mode n)), 20⟩

private theorem dispatch (mode : Fin 2) (n : Nat) :
    CallPair primitives Eq numbering results (source left mode n) (source right mode n) := by
  have paired := link_then_invoke (rename := numbering) respects moduleIso moduleSchedule
    (fun i => by simp [renameVertex, modulePositions]) .nil .head (carry_related mode n) 20
    (unitL := 17) (unitR := 17) (by
      intro exportsL exportsR post linkedL linkedR _
      cases outcome_unique linkedL (linked left)
      cases outcome_unique linkedR (linked right)
      exact .closure .nil initial outputs ordered)
  change DispatchPair primitives Eq (renameVertex modulePositions) numbering results
    ((entry left mode n).start primitives) ((entry right mode n).start primitives) at paired
  rw [start_linked (request := entry left mode n) (linked left),
    start_linked (request := entry right mode n) (linked right)] at paired
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

/-- Both real machines execute a nonempty segment between related fresh
activations. The next body receives data 1 and the advanced store 23. -/
private theorem firstRestart :
    TransGen (Step primitives) (restart left outputs (carry 1 0) (carry 1 0, 20))
      (restart left outputs (carry 1 0) (carry 1 1, 23)) ∧
    TransGen (Step primitives) (restart right outputs (carry 1 0) (carry 1 0, 20))
      (restart right outputs (carry 1 0) (carry 1 1, 23)) :=
  (feedback 1 0 20 (_root_.Part.mem_some _)).steps outputs (carry 1 0) (carry 1 0)

private theorem leftProductive : Feedback.Run primitives (embed left.toTerm) (carry 1 0, 20) := by
  refine ⟨fun n => (carry 1 n, 20 + 3 * n), rfl, ?_⟩
  intro n
  have update : 20 + 3 * (n + 1) = 20 + 3 * n + 3 := by omega
  change Feedback.Iteration primitives (embed left.toTerm) (carry 1 n, 20 + 3 * n)
    (carry 1 (n + 1), 20 + 3 * (n + 1))
  rw [update]
  exact (feedback 1 n (20 + 3 * n) (_root_.Part.mem_some _)).1

private theorem openFixture {sigs : List (Ports T)} (body : Body Op carried sigs) (mode : Fin 2) (n : Nat) :
    Job.openClosure machine (callable body) (carry mode n) =
      .region (code initial body outputs) (carry mode n) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (carry mode n) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph (code initial body outputs))

/-- Productive feedback is independently known on the left. It transports
to the actual right dispatched closure with different body numbering. -/
private theorem divergentCall : InfiniteTrace (Step primitives) (source right 1 0) := by
  apply (dispatch 1 0).infinite_iff.mp
  let target : Feedback.Restart machine Nat := ⟨carried, [[], bodyResults], embed left.toTerm, (carry 1 0, 20)⟩
  let frames : Pending machine carried results := .bind (past := []) (.ret outputs) (carry 1 0) PUnit.unit .empty
  have route : Feedback.Reaches primitives (.region (code initial left outputs) (carry 1 0) PUnit.unit)
      20 target frames :=
    .inside (node := Isomorphism.Invocation.loopVertex initial [[], bodyResults])
      (.theta (.restart (input := target.input) (current := target.input) .refl))
  rw [← openFixture left 1 0] at route
  have productive : Feedback.Productive primitives (.call (callable left) (carry 1 0)) 20 :=
    ⟨target, frames, .call route, leftProductive⟩
  exact productive.infinite .halt

private def pendingL : Pending machine bodyResults bodyResults :=
  .bind (past := [[]]) (.ret tailL) (carry 0 1) (Locals.snoc (past := []) PUnit.unit .nil) .empty

private def pendingR : Pending machine bodyResults bodyResults :=
  .bind (past := []) (embed (.bind idle (fun _ => .ret .nil) (.ret tailR))) (carry 0 1) PUnit.unit .empty

private theorem mapped : numbering.location (.here 1) = .here 0 := rfl

private theorem blockedL :
    BlockAt primitives left.toTerm (carry 0 1) PUnit.unit 23 (.here 1)
      (.blocked (advanceSite 0 1) pendingL 23) := by
  rw [Term.toTerm_toGraph]
  exact .later (idleEval (past := []) PUnit.unit 0 1 23)
    (BlockAt.here (past := [[]]) Op.advance initial (carry 0 1)
      (Locals.snoc (past := []) PUnit.unit .nil) 23 rfl)

private theorem blockedR :
    BlockAt primitives right.toTerm (carry 0 1) PUnit.unit 23 (numbering.location (.here 1))
      (.blocked (advanceSite 0 1) pendingR 23) := by
  rw [Term.toTerm_toGraph, mapped]
  exact BlockAt.here (past := []) Op.advance initial (carry 0 1) PUnit.unit 23 rfl

/-- The undefined primitive is reached after one successful feedback,
with carried input 1 and exact attempt store 23. Its local address goes
from 1 to 0 and its body, θ and caller suffix frames are retained. -/
private theorem finishesBlocked :
    Finishes primitives numbering left right (atCarry 0 0 20)
      (.blocked (advanceSite 0 1) (.loop (embed left.toTerm) pendingL) 23)
      (.blocked (advanceSite 0 1) (.loop (embed right.toTerm) pendingR) 23) :=
  ⟨atCarry 0 1 23, .single (feedback 0 0 20 (_root_.Part.mem_some _)),
    .blocked (.here 1) (.same (carry_related 0 1)) blockedL blockedR⟩

private def blockEndpoint {sigs : List (Ports T)} (body : Body Op carried sigs)
    (pending : Pending machine bodyResults bodyResults) : Config machine Nat results :=
  (Continuation.Partial.Outcome.blocked (advanceSite 0 1)
    (.bind (past := []) (.ret outputs) (carry 0 0) PUnit.unit (.loop (embed body.toTerm) pending)) 23).atStack .halt

private theorem replayBlock {sigs : List (Ports T)} (body : Body Op carried sigs)
    (pending : Pending machine bodyResults bodyResults)
    (ran : Eval primitives (.iteration (embed body.toTerm) (carry 0 0)) 20
      (.blocked (advanceSite 0 1) (.loop (embed body.toTerm) pending) 23)) :
    TerminalPath primitives (source body 0 0) (blockEndpoint body pending) := by
  have evaluated : Eval primitives (.call (callable body) (carry 0 0)) 20
      (.blocked (advanceSite 0 1)
        (.bind (past := []) (.ret outputs) (carry 0 0) PUnit.unit (.loop (embed body.toTerm) pending)) 23) := by
    apply Eval.call
    rw [openFixture]
    exact .bindBlocked (node := Isomorphism.Invocation.loopVertex initial sigs) (.theta ran)
  exact ⟨evaluated.steps .halt, fun _ => (evaluated.blocks .halt).no_step⟩

private theorem blockedCalls :
    TerminalPath primitives (source left 0 0) (blockEndpoint left pendingL) ∧
    TerminalPath primitives (source right 0 0) (blockEndpoint right pendingR) :=
  ⟨replayBlock left pendingL finishesBlocked.eval.1, replayBlock right pendingR finishesBlocked.eval.2⟩

private theorem finishesExited :
    Finishes primitives numbering left right (atCarry 0 2 20)
      (.returned (carry 0 26) 28) (.returned (carry 0 26) 28) :=
  ⟨atCarry 0 3 23, .single (feedback 0 2 20 (_root_.Part.mem_some _)),
    .exited (tag := .control 0) rfl (carry_related 0 26)
      (bodyReturnsL 0 3 23 (_root_.Part.mem_some _)) (bodyReturnsR 0 3 23 (_root_.Part.mem_some _))⟩

private theorem replayExit {sigs : List (Ports T)} (body : Body Op carried sigs)
    (ran : Eval primitives (.iteration (embed body.toTerm) (carry 0 2)) 20 (.returned (carry 0 26) 28)) :
    TerminalPath primitives (source body 0 2) ⟨.returned (output 26 2) .halt, 28⟩ := by
  have evaluated : Eval primitives (.call (callable body) (carry 0 2)) 20 (.returned (output 26 2) 28) := by
    apply Eval.call
    rw [openFixture]
    exact .bind (node := Isomorphism.Invocation.loopVertex initial sigs) (.theta ran) (.ret outputs _ _ _)
  exact ⟨evaluated.steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩

/-- Exit after feedback returns the updated carried data and the saved
original argument in suffix order, at the exact final store 28. -/
private theorem returnedCalls :
    TerminalPath primitives (source left 0 2) ⟨.returned (output 26 2) .halt, 28⟩ ∧
    TerminalPath primitives (source right 0 2) ⟨.returned (output 26 2) .halt, 28⟩ :=
  ⟨replayExit left finishesExited.eval.1, replayExit right finishesExited.eval.2⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Tests
