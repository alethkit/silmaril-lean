module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Tests

open Continuation.Partial
open Continuation.Descent (Pending)
open PartialLink.Invocation (start_error_iff start_linked)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev fn : Function Unit Unit := ⟨[num], [num]⟩
private abbrev carried : Ports T := [global, num]

private inductive Op : Dialect (ValueSort Unit Unit) Unit where
  | seed : Op [num] [num]
  | advance : Op carried (Theta.BodyResults carried)

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .seed, .cons (.data n) .nil => .cons (.data (n + 100)) .nil
    | .advance, input => .cons (.control 0) input

private def numValue (n : Nat) : Tuple machine.Val [num] := .cons (.data n) .nil

private def seedAction (input store : Nat) : _root_.Part (Tuple machine.Val [num] × Nat) :=
  if input = 0 then .none else .some (numValue (input + 7), store + 3)

private def advanceAction (captured : machine.Val global) (payload mode store : Nat) :
    _root_.Part (Tuple machine.Val (Theta.BodyResults carried) × Nat) :=
  if mode = 0 then .none
  else if mode = 1 then .some (.cons (.control 0) (.cons captured (numValue (payload + store))), store + 2)
  else .some (.cons (.control 1) (.cons captured (numValue mode)), store + 1)

private def primitives : Primitives machine Nat where
  step
    | .seed, .cons (.data n) .nil => seedAction n
    | .advance, .cons (.global unit vertex (.data value)) (.cons (.data mode) .nil) =>
      advanceAction (.global unit vertex (.data value)) value mode

private def positions : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

private def ids : GlobalRel := fun left right =>
  left.1 = right.1 ∧ renameVertex positions left.2 = right.2

private theorem respects : ActionsRespect primitives ids := by
  intro _ _ opcode _ _ related store
  cases opcode with
  | seed =>
    cases related with
    | cons number tail =>
      cases number with
      | data v =>
        cases tail
        change ActionRelated machine ids Nat [num] (seedAction v store) (seedAction v store)
        unfold seedAction
        split
        · exact .undefined
        · exact .returned (.cons (.data _) .nil) _
  | advance =>
    cases related with
    | cons global tail =>
      cases global with
      | @global _ leftUnit rightUnit leftVertex rightVertex _ _ identity payload =>
        cases payload with
        | data v =>
          cases tail with
          | cons flag tail =>
            cases flag with
            | data mode =>
              cases tail
              change ActionRelated machine ids Nat (Theta.BodyResults carried)
                (advanceAction (.global leftUnit leftVertex (.data v)) v mode store)
                (advanceAction (.global rightUnit rightVertex (.data v)) v mode store)
              unfold advanceAction
              split
              · exact .undefined
              · split
                · exact .returned (.cons (.control 0) (.cons (.global identity (.data _)) (.cons (.data _) .nil))) _
                · exact .returned (.cons (.control 1) (.cons (.global identity (.data _)) (.cons (.data _) .nil))) _

private def seedTail : Term Op [num] [[num]] [] [num] :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def seedTerm : Term Op [num] [] [[num]] [num] :=
  .bind ⟨[num], .simple .seed, .cons (.arg .head) .nil, fun i => i.elim0⟩ (fun i => i.elim0) seedTail

private def delta (past : List (Ports T)) : DeltaTerm Op [num] past (.data ()) :=
  ⟨[num], .cons (.arg .head) .nil, [[num]], seedTerm⟩

private def initial : Wires carried [] carried :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

private def bodyResults : Wires carried [Theta.BodyResults carried] (Theta.BodyResults carried) :=
  .cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head))
    (.cons (.output (0 : Fin 1) (.tail (.tail .head))) .nil))

private def body : Term Op carried [] [Theta.BodyResults carried] (Theta.BodyResults carried) :=
  .bind ⟨carried, .simple .advance, initial, fun i => i.elim0⟩ (fun i => i.elim0) (.ret bodyResults)

private def outputs : Wires carried [carried] [num] :=
  .cons (.output (0 : Fin 1) (.tail .head)) .nil

private def code : NestedTheta.Term (Instruction Op) carried [] [carried] [num] :=
  .bind (loopVertex initial [Theta.BodyResults carried]) (fun _ => embed body) (.ret outputs)

private def lambda {past : List (Ports T)} (captured : Origin [num] past global) :
    LambdaTerm Op [num] past fn :=
  ⟨[global], .cons captured .nil, [carried], code⟩

private def left : OmegaTerm Op [num] [fn.port] [[global], [], [fn.port]] :=
  ⟨.bind (.delta (delta [])) <| .bind (.phi (emptyPhi Op [num] _)) <|
    .bind (.lambda (lambda (.output (0 : Fin 2) .head))) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private def right : OmegaTerm Op [num] [fn.port] [[], [global], [fn.port]] :=
  ⟨.bind (.phi (emptyPhi Op [num] [])) <| .bind (.delta (delta [[]])) <|
    .bind (.lambda (lambda (.output (1 : Fin 2) .head))) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private theorem seedIso : Graph.Isomorphic Op seedTerm.toGraph seedTerm.toGraph := by
  refine .intro rfl rfl (Equiv.refl _) (fun _ => rfl) ?_ rfl ?_
  · intro i
    exact Fin.cases rfl (fun j => j.elim0) i
  · intro i
    refine Fin.cases ?_ (fun j => j.elim0) i
    intro arm
    exact arm.elim0

private theorem iso : left.toGraph.RenumberedBy right.toGraph positions := by
  refine ⟨?_, rfl⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .delta ⟨⟨rfl, rfl⟩, seedIso⟩
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact .phi ⟨⟨rfl, rfl⟩, fun i => i.elim0⟩
    · refine Fin.cases ?_ (fun l => l.elim0) k
      exact .lambda ⟨⟨rfl, rfl⟩, .refl _⟩

private theorem ordered : Ordered Op (renameVertex positions) [num] [fn.port]
    left.toGraph.toTerm.region right.toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .emptyRight (.bind rfl (.delta ⟨rfl, rfl⟩ seedTerm) (.emptyLeft
    (.bind rfl (.lambda ⟨⟨rfl, rfl⟩, .refl _⟩) (.ret _ _))))

private def globalAt (vertex : Nat) : machine.Val global := .global 73 vertex (.data (8 : Nat))

private def carry (vertex mode : Nat) : Tuple machine.Val carried := .cons (globalAt vertex) (numValue mode)

private def callee (vertex : Nat) : machine.Val fn.port := .closure (.cons (globalAt vertex) .nil) code.toGraph

private def published (vertex : Nat) : Tuple machine.Val [fn.port] := .cons (callee vertex) .nil

private def seedSite (input : Nat) : Site machine :=
  ⟨[num], [num], .seed, fun i => i.elim0, fun i => embed (i.elim0), numValue input⟩

private theorem openSeed (flag : Nat) :
    Job.region (m := machine) (past := []) (embed seedTerm.toGraph.toTerm) (numValue flag) PUnit.unit =
      .region (embed seedTerm) (numValue flag) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) (embed term) (numValue flag) PUnit.unit)
    (Term.toTerm_toGraph seedTerm)

private theorem seedReturns :
    Eval primitives (.region (embed seedTerm.toGraph.toTerm) (numValue 1) PUnit.unit) 20
      (.returned (numValue 8) 23) := by
  rw [openSeed 1]
  refine Eval.bind (value := numValue 8) (middle := 23) ?_ ?_
  · refine Eval.primitive (seedSite 1) ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

private def seedPending : Pending machine [num] [num] :=
  .bind (past := []) (embed seedTail) (numValue 0) PUnit.unit .empty

private theorem seedBlocks :
    Eval primitives (.region (embed seedTerm.toGraph.toTerm) (numValue 0) PUnit.unit) 20
      (.blocked (seedSite 0) seedPending 20) := by
  rw [openSeed 0]
  exact .bindBlocked (.primitiveBlocked (seedSite 0) 20 rfl)

private def failure (vertex : Nat) : Failure machine Nat := ⟨73, vertex, seedSite 0, 20⟩

private theorem leftFails : Links primitives 73 left.toGraph (numValue 0) 20 (.undefined (failure 0)) :=
  .stop (LinksDelta.undefined seedBlocks)

private theorem rightFails : Links primitives 73 right.toGraph (numValue 0) 20 (.undefined (failure 1)) :=
  .bind (values := (.nil : Tuple machine.Val [])) (middle := 20) rfl (.stop (LinksDelta.undefined seedBlocks))

private theorem leftReady : Links primitives 73 left.toGraph (numValue 1) 20 (.linked (published 0) 23) := by
  refine LinksTable.bind (values := (.cons (globalAt 0) .nil : Tuple machine.Val [global])) (middle := 23)
    (LinksDelta.linked seedReturns) ?_
  exact .bind (values := (.nil : Tuple machine.Val [])) (middle := 23) rfl
    (.bind (values := published 0) (middle := 23) rfl (.ret _ _ _ _))

private theorem rightReady : Links primitives 73 right.toGraph (numValue 1) 20 (.linked (published 1) 23) := by
  refine LinksTable.bind (values := (.nil : Tuple machine.Val [])) (middle := 20) rfl ?_
  exact .bind (values := (.cons (globalAt 1) .nil : Tuple machine.Val [global])) (middle := 23)
    (LinksDelta.linked seedReturns) (.bind (values := published 1) (middle := 23) rfl (.ret _ _ _ _))

private def flag (enabled : Bool) : Nat := if enabled then 1 else 0

private abbrev leftRequest (enabled : Bool) (mode : Nat) :=
  request 73 left.toGraph (numValue (flag enabled)) .head (numValue mode) 20

private abbrev rightRequest (enabled : Bool) (mode : Nat) :=
  request 73 right.toGraph (numValue (flag enabled)) .head (numValue mode) 20

private theorem paired (enabled : Bool) (mode : Nat) :
    ObservationsRelated primitives ids (renameVertex positions) [num]
      ((leftRequest enabled mode).start primitives) ((rightRequest enabled mode).start primitives) := by
  apply link_then_invoke_related respects iso ordered (fun _ => ⟨rfl, rfl⟩) (.cons (.data _) .nil)
    .head (.cons (.data _) .nil) 20
  intro exportsL exportsR post linksL linksR
  cases enabled with
  | false => cases outcome_unique linksL leftFails
  | true =>
    obtain ⟨rfl, rfl⟩ := Outcome.linked.inj (outcome_unique linksL leftReady)
    obtain ⟨rfl, _⟩ := Outcome.linked.inj (outcome_unique linksR rightReady)
    exact .closure (.theta initial body outputs)

private def source (vertex mode : Nat) : Config machine Nat [num] :=
  ⟨Continuation.start (.call (callee vertex) (numValue mode)), 23⟩

private theorem startedL (mode : Nat) : (leftRequest true mode).start primitives = .ok (source 0 mode) :=
  start_linked (request := leftRequest true mode) (primitives := primitives) leftReady

private theorem startedR (mode : Nat) : (rightRequest true mode).start primitives = .ok (source 1 mode) :=
  start_linked (request := rightRequest true mode) (primitives := primitives) rightReady

private theorem openCallee (vertex mode : Nat) :
    Job.openClosure machine (callee vertex) (numValue mode) = .region code (carry vertex mode) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (carry vertex mode) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph code)

private def advanceSite (vertex mode : Nat) : Site machine :=
  ⟨carried, Theta.BodyResults carried, .advance, fun i => i.elim0, fun i => embed (i.elim0), carry vertex mode⟩

private theorem bodyReturns (vertex : Nat) :
    Eval primitives (.region (embed body) (carry vertex 1) PUnit.unit) 23
      (.returned (.cons (.control 0) (carry vertex 31)) 25) := by
  refine Eval.bind (value := .cons (.control 0) (carry vertex 31)) (middle := 25) ?_ ?_
  · refine Eval.primitive (advanceSite vertex 1) ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

private theorem returned (vertex : Nat) :
    Eval primitives (.call (callee vertex) (numValue 1)) 23 (.returned (numValue 31) 25) := by
  apply Eval.call
  rw [openCallee]
  exact .bind (value := carry vertex 31) (middle := 25) (.theta (.stop (bodyReturns vertex) rfl)) (.ret _ _ _ _)

private def bodyPending (vertex : Nat) : Pending machine (Theta.BodyResults carried) (Theta.BodyResults carried) :=
  .bind (past := []) (embed (.ret bodyResults)) (carry vertex 0) PUnit.unit .empty

private def pending (vertex : Nat) : Pending machine (Theta.BodyResults carried) [num] :=
  .bind (past := []) (.ret outputs) (carry vertex 0) PUnit.unit (.loop (embed body) (bodyPending vertex))

private theorem invocationBlocks (vertex : Nat) :
    Eval primitives (.call (callee vertex) (numValue 0)) 23 (.blocked (advanceSite vertex 0) (pending vertex) 23) := by
  apply Eval.call
  rw [openCallee]
  exact .bindBlocked (.theta (.loopBlocked (.bindBlocked (.primitiveBlocked (advanceSite vertex 0) 23 rfl))))

private theorem loopRuns : Feedback.Run primitives (embed body) (carry 0 2, 23) := by
  refine ⟨fun n => (carry 0 2, 23 + n), rfl, fun n => ⟨.control 1, ?_, rfl⟩⟩
  refine Eval.bind (value := .cons (.control 1) (carry 0 2)) (middle := 23 + (n + 1)) ?_ ?_
  · refine Eval.primitive (advanceSite 0 2) ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

private theorem leftProductive : Feedback.Productive primitives (.call (callee 0) (numValue 2)) 23 := by
  let target : Feedback.Restart machine Nat :=
    ⟨carried, [Theta.BodyResults carried], embed body, carry 0 2, 23⟩
  let frames : Pending machine carried [num] := .bind (past := []) (.ret outputs) (carry 0 2) PUnit.unit .empty
  refine ⟨target, frames, .call ?_, loopRuns⟩
  rw [openCallee]
  exact .inside (node := loopVertex initial [Theta.BodyResults carried])
    (.theta (.restart (input := target.input) (current := target.input) .refl))

-- A checked renumbering moves the initialized global from 0 to 1.
-- The exported λ captures the corresponding allocation on each side.
example : (leftRequest false 0).start primitives = .error (failure 0) ∧
    (rightRequest false 0).start primitives = .error (failure 1) :=
  ⟨start_error_iff.mpr leftFails, start_error_iff.mpr rightFails⟩

example : (leftRequest true 1).start primitives = .ok (source 0 1) ∧
    (rightRequest true 1).start primitives = .ok (source 1 1) ∧
    Relation.ReflTransGen (Step primitives) (source 0 1) ⟨.returned (numValue 31) .halt, 25⟩ ∧
    Relation.ReflTransGen (Step primitives) (source 1 1) ⟨.returned (numValue 31) .halt, 25⟩ :=
  ⟨startedL 1, startedR 1, (returned 0).steps .halt, (returned 1).steps .halt⟩

private def stopped (vertex : Nat) : Config machine Nat [num] :=
  ⟨.eval (advanceSite vertex 0).job ((pending vertex).push .halt), 23⟩

example : SitesRelated machine ids (advanceSite 0 0) (advanceSite 1 0) ∧
    Relation.ReflTransGen (Step primitives) (source 0 0) (stopped 0) ∧ (stopped 0).Blocked primitives ∧
    Relation.ReflTransGen (Step primitives) (source 1 0) (stopped 1) ∧ (stopped 1).Blocked primitives :=
  ⟨.same (.cons (.global ⟨rfl, rfl⟩ (.data _)) (.cons (.data _) .nil)),
    (invocationBlocks 0).steps .halt, (invocationBlocks 0).blocks .halt,
    (invocationBlocks 1).steps .halt, (invocationBlocks 1).blocks .halt⟩

-- The right infinite execution follows from transport of the productive
-- left execution. Every θ iteration completes and changes the store.
example : InfiniteTrace (Step primitives) (source 1 2) := by
  have both := paired true 2
  rw [startedL 2, startedR 2] at both
  exact both.infinite_iff.mp (leftProductive.infinite .halt)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Tests
