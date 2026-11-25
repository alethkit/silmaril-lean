module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Tests

open Continuation.Partial (Primitives Eval Site Config)
open Continuation.Descent (Pending)
open Isomorphism.Invocation (request)
open PartialLink.Invocation (start_linked)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev result : Ports T := [num]
private abbrev params : Ports T := [.control 2, num]
private abbrev fn : Function Unit Unit := ⟨params, result⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit where
  | tick : Op result result
  | guard : Op result result

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .tick, input => input
    | .guard, input => input

private def number (n : Nat) : Tuple machine.Val result := .cons (.data n) .nil

private def guardAction (n store : Nat) : _root_.Part (Tuple machine.Val result × Nat) :=
  if n = 0 then .none else .some (number (n + store), store * 2)

private def primitives : Primitives machine Nat where
  step
    | .tick, input => fun store => .some (input, store + 3)
    | .guard, .cons (.data n) .nil => guardAction n

private theorem respects : ActionsRespect primitives Eq := by
  intro _ _ opcode _ _ related store
  cases opcode with
  | tick => exact .returned related _
  | guard =>
    cases related with
    | cons value tail =>
      cases value with
      | data n =>
        cases tail
        change ActionRelated machine Eq Nat result (guardAction n store) (guardAction n store)
        unfold guardAction
        split
        · exact .undefined
        · exact .returned (.cons (.data _) .nil) _

private def primitiveNode {args : Ports T} {past : List (Ports T)} (opcode : Op result result)
    (origin : Origin args past num) : Node Op args past result :=
  ⟨result, .simple opcode, .cons origin .nil, fun i => i.elim0⟩

private def tick : Node Op params [] result := primitiveNode .tick (.arg (.tail .head))

private def idle {past : List (Ports T)} : Node Op params past [] :=
  emptyGamma (entry := []) (extra := 0) (.cons (.arg .head) .nil)

private def armSigs : Fin 2 → List (Ports T) := Fin.cases [result] (fun _ => [])

private def armBody : (tag : Fin 2) → Term Op result [] (armSigs tag) result :=
  Fin.cases
    (.bind (primitiveNode .guard (.arg .head)) (fun i => i.elim0)
      (.ret (.cons (.output (0 : Fin 1) .head) .nil)))
    (fun _ => .ret (.cons (.arg .head) .nil))

private def branch {past : List (Ports T)} (fromTick : Origin params past num) : Node Op params past result :=
  ⟨params, .gamma 0, .cons (.arg .head) (.cons fromTick .nil), armSigs⟩

private def tailResultsL : Wires params [result, [], result] result :=
  .cons (.output (2 : Fin 3) .head) .nil

private def tailResultsR : Wires params [result, result, []] result :=
  .cons (.output (1 : Fin 3) .head) .nil

private def leftBody : Term Op params [] [result, [], result] result :=
  .bind tick (fun i => i.elim0) <|
    .bind idle (fun _ => .ret .nil) <|
      .bind (branch (.output (0 : Fin 2) .head)) armBody (.ret tailResultsL)

private def rightBody : Term Op params [] [result, result, []] result :=
  .bind tick (fun i => i.elim0) <|
    .bind (branch (.output (0 : Fin 1) .head)) armBody <|
      .bind idle (fun _ => .ret .nil) (.ret tailResultsR)

private def numbering : Renaming := .region (Equiv.swap 1 2) (fun _ _ => .identity)

private theorem childZero : GraphRenumbered Op .identity (armBody 0).toGraph (armBody 0).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) ?_ rfl ?_
  · intro i
    exact Fin.cases rfl (fun j => j.elim0) i
  · intro i
    refine Fin.cases ?_ (fun j => j.elim0) i
    intro branch
    exact branch.elim0

private theorem childOne : GraphRenumbered Op .identity (armBody 1).toGraph (armBody 1).toGraph :=
  .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) rfl (fun i => i.elim0)

private theorem idleChild : GraphRenumbered Op .identity
    (Term.ret (Op := Op) (args := []) (past := []) .nil).toGraph
    (Term.ret (Op := Op) (args := []) (past := []) .nil).toGraph :=
  .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) rfl (fun i => i.elim0)

private theorem allThree {p : Fin 3 → Prop} (first : p 0) (second : p 1) (third : p 2) (i : Fin 3) : p i :=
  Fin.cases first (Fin.cases second (Fin.cases third (fun j => j.elim0))) i

private theorem graph : GraphRenumbered Op numbering leftBody.toGraph rightBody.toGraph := by
  let positions : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
  have labels : ∀ i, (leftBody.toGraph.nodes i).label = (rightBody.toGraph.nodes (positions i)).label := by
    exact allThree rfl rfl rfl
  refine .intro rfl rfl positions ?_ labels ?_ rfl ?_
  · exact allThree rfl rfl rfl
  · exact allThree rfl rfl rfl
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro arm
      exact arm.elim0
    · refine Fin.cases ?_ (fun i => ?_) i
      · intro _
        exact idleChild
      · refine Fin.cases ?_ (fun i => i.elim0) i
        intro arm
        refine Fin.cases ?_ (fun j => ?_) arm
        · exact childZero
        · exact Fin.cases childOne (fun i => i.elim0) j

private theorem armSchedule (tag : Fin 2) : Schedule Op .identity (armBody tag) (armBody tag) := by
  refine Fin.cases ?_ (fun j => ?_) tag
  · refine Schedule.bind (Shape.simple Op.guard) _ _ rfl rfl (fun i => i.elim0) ?_
    exact .ret _ _ rfl
  · exact Fin.cases (.ret _ _ rfl) (fun i => i.elim0) j

private theorem ordered : OrderedGraph numbering leftBody.toGraph rightBody.toGraph := by
  refine ⟨graph, ?_⟩
  rw [Term.toTerm_toGraph, Term.toTerm_toGraph]
  refine Schedule.bind (Shape.simple Op.tick) _ _ rfl rfl (fun i => i.elim0) ?_
  refine Schedule.emptyLeft idle.inputs ?_
  refine Schedule.bind (Shape.gamma (Op := Op) (entry := result) (exit := result) 0)
    _ _ rfl rfl armSchedule ?_
  refine Schedule.emptyRight idle.inputs ?_
  exact .ret tailResultsL tailResultsR rfl

private def omega {sigs : List (Ports T)} (body : Graph Op params [] sigs result) :
    Omega Op [] [fn.port] [[fn.port]] :=
  (⟨.bind (.lambda ⟨[], .nil, sigs, embed body.toTerm⟩)
      (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩ :
    OmegaTerm Op [] [fn.port] [[fn.port]]).toGraph

private def callable {sigs : List (Ports T)} (body : Graph Op params [] sigs result) : machine.Val fn.port :=
  .closure (.nil : Tuple machine.Val []) (embed body.toTerm).toGraph

private def input (tag : Fin 2) (n : Nat) : Tuple machine.Val params := .cons (.control tag) (number n)

private abbrev entry {sigs : List (Ports T)} (body : Graph Op params [] sigs result) (tag : Fin 2) (n : Nat) :=
  request (m := machine) 13 (omega body) .nil .head (input tag n) 20

private theorem linked {sigs : List (Ports T)} (body : Graph Op params [] sigs result) :
    Links primitives 13 (omega body) .nil 20 (.linked (.cons (callable body) .nil) 20) :=
  .bind (values := .cons (callable body) .nil) (middle := 20) rfl (.ret _ _ _ _)

/-- The actual exported calls invoke different numbered bodies under the
same store and arguments. Both exports come from partial linking. -/
private theorem dispatched (tag : Fin 2) (n : Nat) :
    ∃ sourceL sourceR,
      (entry leftBody.toGraph tag n).start primitives = .ok sourceL ∧
      (entry rightBody.toGraph tag n).start primitives = .ok sourceR ∧
      CallPair primitives Eq numbering result sourceL sourceR :=
  start_linked_calls respects (linked _) (linked _) rfl (.closure .nil ordered)
    (.cons (.control tag) (.cons (ValueRelated.data (m := machine) (t := ()) n) .nil))

private def guardSite (n : Nat) : Site machine :=
  ⟨result, result, .guard, fun i => i.elim0, fun i => embed (i.elim0), number n⟩

private abbrev afterGuard : Wires result [result] result := .cons (.output (0 : Fin 1) .head) .nil

private def guardPending : Pending machine result result :=
  .bind (past := []) (.ret afterGuard) (number 0) PUnit.unit .empty

private def leftPending : Pending machine result result :=
  .bind (past := [result, []]) (.ret tailResultsL) (input 0 0)
    ((Locals.snoc (past := []) PUnit.unit (number 0)).snoc .nil) guardPending

private def rightPending : Pending machine result result :=
  .bind (past := [result]) (embed (.bind idle (fun _ => .ret .nil) (.ret tailResultsR))) (input 0 0)
    (Locals.snoc (past := []) PUnit.unit (number 0)) guardPending

private theorem mapped : numbering.location (.arm 2 0 (.here 0)) = .arm 1 0 (.here 0) := rfl

/-- The selected guard sees the successful prefix's effect. Moving γ
relocates the block and changes the actual pending suffix. -/
private theorem selectedBlocks :
    BlockAt primitives leftBody (input 0 0) PUnit.unit 20 (.arm 2 0 (.here 0))
      (.blocked (guardSite 0) leftPending 23) ∧
    BlockAt primitives rightBody (input 0 0) PUnit.unit 20 (numbering.location (.arm 2 0 (.here 0)))
      (.blocked (guardSite 0) rightPending 23) := by
  have ticked : Eval primitives (nodeJob tick (fun i => i.elim0) (input 0 0) PUnit.unit)
      20 (.returned (number 0) 23) :=
    Eval.primitive ⟨result, result, .tick, fun i => i.elim0, fun i => embed (i.elim0), number 0⟩
      (_root_.Part.mem_some _)
  have empty : Eval primitives (nodeJob (idle (past := [result])) (fun _ => .ret .nil)
      (input 0 0) (Locals.snoc (past := []) PUnit.unit (number 0))) 23 (.returned .nil 23) :=
    Eval.gamma (tag := 0) (Eval.ret (past := []) .nil .nil PUnit.unit 23)
  refine ⟨.later ticked (.later empty ?_), .later ticked ?_⟩
  · exact .arm (tag := 0) rfl (BlockAt.here (past := []) Op.guard (.cons (.arg .head) .nil) (number 0) PUnit.unit 23 rfl)
  · rw [mapped]
    exact .arm (tag := 0) rfl (BlockAt.here (past := []) Op.guard (.cons (.arg .head) .nil) (number 0) PUnit.unit 23 rfl)

private def source {sigs : List (Ports T)} (body : Graph Op params [] sigs result) (tag : Fin 2) (n : Nat) :
    Config machine Nat result :=
  ⟨Continuation.start (.call (callable body) (input tag n)), 20⟩

private theorem exactDispatch (tag : Fin 2) (n : Nat) :
    CallPair primitives Eq numbering result
      (source leftBody.toGraph tag n) (source rightBody.toGraph tag n) := by
  obtain ⟨left, right, startedL, startedR, paired⟩ := dispatched tag n
  rw [start_linked (request := entry leftBody.toGraph tag n) (linked _)] at startedL
  rw [start_linked (request := entry rightBody.toGraph tag n) (linked _)] at startedR
  cases startedL
  cases startedR
  exact paired

private theorem evalCall {sigs : List (Ports T)} {term : Term Op params [] sigs result} {tag : Fin 2}
    {n : Nat} {outcome : Continuation.Partial.Outcome machine Nat result}
    (body : Eval primitives (.region (embed term) (input tag n) PUnit.unit) 20 outcome) :
    Eval primitives (.call (callable term.toGraph) (input tag n)) 20 outcome := by
  apply Eval.call
  change Eval primitives (.region (embed term.toGraph.toTerm).toGraph.toTerm (input tag n) PUnit.unit) 20 outcome
  rw [NestedTheta.Term.toTerm_toGraph, Term.toTerm_toGraph]
  exact body

private theorem terminalBlock {sigs : List (Ports T)} {term : Term Op params [] sigs result}
    {whereAt : Location} {pending : Pending machine result result}
    (body : BlockAt primitives term (input 0 0) PUnit.unit 20 whereAt (.blocked (guardSite 0) pending 23)) :
    TerminalPath primitives (source term.toGraph 0 0) ⟨.eval (guardSite 0).job (pending.push .halt), 23⟩ :=
  let call := evalCall body.eval
  ⟨call.steps .halt, fun _ => (call.blocks .halt).no_step⟩

private def selectedSite (config : Config machine Nat result) : Option (Site machine) :=
  (Continuation.Partial.selectedPrimitive config.control).map (·.site)

private theorem selectedSite_atBlock (site : Site machine) (pending : Pending machine site.outs result) (store : Nat) :
    selectedSite ⟨.eval site.job (pending.push .halt), store⟩ = some site := by
  cases site
  rfl

/-- Reflect the actual right-hand blocked endpoint. The left execution
reaches a related typed diagnostic at exactly the right attempt store. -/
private theorem blockTransport :
    ∃ (site : Site machine) (pending : Pending machine site.outs result),
      SitesRelated machine Eq site (guardSite 0) ∧
      TerminalPath primitives (source leftBody.toGraph 0 0) ⟨.eval site.job (pending.push .halt), 23⟩ := by
  have observedR := terminalBlock selectedBlocks.2
  cases exactDispatch 0 0 with
  | invoked _ evaluation machineL machineR =>
    have matched := (machineR _).mp observedR
    cases evaluation with
    | returned =>
      cases congrArg Config.result matched
    | @blocked siteL siteR pendingL pendingR stopped _ sites _ _ =>
      have sameStore : 23 = stopped := congrArg Config.store matched
      have diagnosed := congrArg selectedSite matched
      have rightSite := selectedSite_atBlock (guardSite 0) rightPending 23
      have pairedSite := selectedSite_atBlock siteR pendingR stopped
      have sameSite := Option.some.inj (rightSite.symm.trans (diagnosed.trans pairedSite))
      exact ⟨siteL, pendingL, sameSite.symm ▸ sites,
        (machineL _).mpr (congrArg (Config.mk (.eval siteL.job (pendingL.push .halt))) sameStore)⟩

private theorem tickEval (tag : Fin 2) (n : Nat) :
    Eval primitives (nodeJob tick (fun i => i.elim0) (input tag n) PUnit.unit) 20 (.returned (number n) 23) :=
  Eval.primitive ⟨result, result, .tick, fun i => i.elim0, fun i => embed (i.elim0), number n⟩ (_root_.Part.mem_some _)

private theorem idleEval (tag : Fin 2) (n : Nat) :
    Eval primitives (nodeJob (idle (past := [result])) (fun _ => .ret .nil)
      (input tag n) (Locals.snoc (past := []) PUnit.unit (number n))) 23 (.returned .nil 23) :=
  Eval.gamma (tag := tag) (cs := fun _ => []) (children := fun _ => .ret .nil)
    (Eval.ret (past := []) .nil .nil PUnit.unit 23)

private theorem sameNumber {left right : Tuple machine.Val result} (values : TupleRelated machine Eq left right) :
    left = right := by
  cases values with
  | cons value tail =>
    cases value
    cases tail
    rfl

private theorem transportReturn {tag : Fin 2} {n expected store : Nat}
    (body : Eval primitives (.region (embed leftBody) (input tag n) PUnit.unit) 20
      (.returned (number expected) store)) :
    TerminalPath primitives (source rightBody.toGraph tag n) ⟨.returned (number expected) .halt, store⟩ := by
  let call := evalCall (term := leftBody) body
  have observedL : TerminalPath primitives (source leftBody.toGraph tag n)
      ⟨.returned (number expected) .halt, store⟩ :=
    ⟨call.steps .halt, fun _ stepped => _root_.Part.notMem_none _ stepped⟩
  cases exactDispatch tag n with
  | invoked _ evaluation machineL machineR =>
    have matched := (machineL _).mp observedL
    cases evaluation with
    | @returned _ _ finalStore values _ _ =>
      have sameResult := congrArg (fun tuple => (⟨.returned tuple .halt, finalStore⟩ : Config machine Nat result))
        (sameNumber values)
      exact (machineR _).mpr (matched.trans sameResult)
    | blocked =>
      cases congrArg Config.result matched

/-- With the same zero input, selecting arm 1 skips the undefined guard.
The right invocation retains exactly the prefix's store update. -/
private theorem skipReturns :
    TerminalPath primitives (source rightBody.toGraph 1 0) ⟨.returned (number 0) .halt, 23⟩ := by
  apply transportReturn
  refine Eval.bind (tickEval 1 0) (Eval.bind (idleEval 1 0) ?_)
  refine Eval.bind (middle := 23) (value := number 0) ?_ (.ret _ _ _ _)
  exact Eval.gamma (tag := 1) (cs := armSigs) (children := fun i => embed (armBody i))
    (Eval.ret (past := []) _ _ PUnit.unit 23)

/-- With a defined guard, the selected action reads the prefix's store
23 and doubles it. This order gives result 28 and final store 46. -/
private theorem selectedReturns :
    TerminalPath primitives (source rightBody.toGraph 0 5) ⟨.returned (number 28) .halt, 46⟩ := by
  apply transportReturn
  refine Eval.bind (tickEval 0 5) (Eval.bind (idleEval 0 5) ?_)
  refine Eval.bind (middle := 46) (value := number 28) ?_ (.ret _ _ _ _)
  apply Eval.gamma (tag := 0) (cs := armSigs) (children := fun i => embed (armBody i))
  exact Eval.bind (middle := 46) (value := number 28)
    (Eval.primitive (guardSite 5) (_root_.Part.mem_some _)) (.ret _ _ _ _)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Tests
