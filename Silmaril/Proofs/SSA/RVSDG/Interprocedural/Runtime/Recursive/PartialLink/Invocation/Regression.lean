module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Tests

open Continuation.Partial (Config Eval Primitives Site Step)
open Continuation.Descent (Pending)

private abbrev T := Ty Unit Unit
private abbrev number : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev fn : Function Unit Unit := ⟨[number], [number]⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | initialize : Op [number] [number]
  | observe : Op [global, number] [number]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .initialize, .cons (.data n) .nil => .cons (.data (n + 100)) .nil
    | .observe, .cons (.global _ _ (.data captured)) (.cons (.data argument) .nil) =>
      .cons (.data (captured + argument)) .nil

private def numberValue (n : Nat) : Tuple machine.Val [number] := .cons (.data n) .nil

private def actions : Continuation.Partial.Executable.Actions machine Nat where
  step
    | .initialize, .cons (.data n) .nil => fun store =>
      let input : Nat := n
      if input = 0 then .none else .some (numberValue (input + 10), store + 5)
    | .observe, .cons (.global _ _ (.data captured)) (.cons (.data argument) .nil) => fun store =>
      let value : Nat := captured
      let input : Nat := argument
      if input = 0 then .none else .some (numberValue (value + input + store), store + 2)

private abbrev primitives : Primitives machine Nat := actions.toPrimitives

private def initTail : Term Op [number] [[number]] [] [number] :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def initTerm : Term Op [number] [] [[number]] [number] :=
  .bind ⟨[number], .simple .initialize, .cons (.arg .head) .nil, fun i => i.elim0⟩
    (fun i => i.elim0) initTail

private def delta : DeltaTerm Op [number] [] (.data ()) :=
  ⟨[number], .cons (.arg .head) .nil, [[number]], initTerm⟩

private def observeNode : NestedTheta.Node (Instruction Op) [global, number] [] [number] :=
  ⟨[global, number], .base (.simple (.primitive .observe)),
    .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), fun i => i.elim0⟩

private def bodyTail : NestedTheta.Term (Instruction Op) [global, number] [[number]] [] [number] :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def body : NestedTheta.Term (Instruction Op) [global, number] [] [[number]] [number] :=
  .bind observeNode (fun i => i.elim0) bodyTail

private def lambda : LambdaTerm Op [number] [[global]] fn :=
  ⟨[global], .cons (.output (0 : Fin 1) .head) .nil, [[number]], body⟩

private def graph : Omega Op [number] [fn.port] [[global], [fn.port]] :=
  OmegaTerm.toGraph ⟨.bind (.delta delta) <| .bind (.lambda lambda) <|
    .ret (.cons (.output (1 : Fin 2) .head) .nil)⟩

private def request (input argument : Nat) : Request machine Nat [number] :=
  ⟨73, [number], [fn.port], [[global], [fn.port]], graph, numberValue input,
    [number], .head, numberValue argument, 20⟩

private def captured : machine.Val global := .global 73 0 (.data (12 : Nat))

private def callee : machine.Val fn.port := .closure (.cons captured .nil) body.toGraph

private def published : Tuple machine.Val [fn.port] := .cons callee .nil

private def initSite (n : Nat) : Site machine :=
  ⟨[number], [number], .initialize, fun i => i.elim0, fun i => embed (i.elim0), numberValue n⟩

private def linkFailure : Failure machine Nat := ⟨73, 0, initSite 0, 20⟩

private theorem initOpened (input : Nat) :
    initializerJob delta.toGraph (numberValue input) (PUnit.unit : Locals machine.Val []) =
      .region (embed initTerm) (numberValue input) PUnit.unit := by
  simp only [initializerJob, DeltaTerm.toGraph, Term.toTerm_toGraph]; rfl

private theorem linkBlocked (argument : Nat) :
    (request 0 argument).Links primitives (.undefined linkFailure) := by
  refine LinksTable.stop ?_
  change LinksVertex primitives 73 (numberValue 0) (past := []) PUnit.unit (.delta delta.toGraph)
    20 (.undefined linkFailure)
  let pending : Pending machine [number] [number] :=
    .bind (past := []) (embed initTail) (numberValue 0) PUnit.unit .empty
  refine LinksDelta.undefined (pending := pending) ?_
  erw [initOpened 0]
  exact Eval.bindBlocked (.primitiveBlocked (initSite 0) 20 rfl)

private theorem linked (argument : Nat) :
    (request 2 argument).Links primitives (.linked published 25) := by
  refine LinksTable.bind (values := (.cons captured .nil : Tuple machine.Val [global])) (middle := 25) ?_ ?_
  · change LinksVertex primitives 73 (numberValue 2) (past := []) PUnit.unit (.delta delta.toGraph)
      20 (.linked (.cons captured .nil) 25)
    refine LinksDelta.linked (initialized := numberValue 12) ?_
    erw [initOpened 2]
    exact Eval.bind (value := numberValue 12) (middle := 25)
      (.primitive (initSite 2) (_root_.Part.mem_some _)) (.ret _ _ _ _)
  · exact LinksTable.bind (values := published) (middle := 25) rfl (.ret _ _ _ _)

private def source (argument : Nat) : Config machine Nat [number] :=
  ⟨Continuation.start (.call callee (numberValue argument)), 25⟩

private theorem started (argument : Nat) : (request 2 argument).start primitives = .ok (source argument) :=
  start_linked (linked argument)

private theorem opened (argument : Nat) :
    Job.openClosure machine callee (numberValue argument) =
      .region body (.cons captured (numberValue argument)) PUnit.unit :=
  congrArg (fun term => Job.region (m := machine) (past := []) term
    (.cons captured (numberValue argument)) PUnit.unit) (NestedTheta.Term.toTerm_toGraph body)

private def invokeSite (argument : Nat) : Site machine :=
  ⟨[global, number], [number], .observe, fun i => i.elim0, fun i => i.elim0,
    .cons captured (numberValue argument)⟩

private def saved : Pending machine [number] [number] :=
  .bind (past := []) bodyTail (.cons captured (numberValue 0)) PUnit.unit .empty

private theorem invokedBlock :
    Eval primitives (.call callee (numberValue 0)) 25 (.blocked (invokeSite 0) saved 25) := by
  apply Eval.call
  rw [opened 0]
  exact .bindBlocked (.primitiveBlocked (invokeSite 0) 25 rfl)

private theorem invokedReturn :
    Eval primitives (.call callee (numberValue 1)) 25 (.returned (numberValue 38) 27) := by
  apply Eval.call
  rw [opened 1]
  exact .bind (value := numberValue 38) (middle := 27)
    (.primitive (invokeSite 1) (_root_.Part.mem_some _)) (.ret _ _ _ _)

-- Both invocations supply argument 0. The initializer failure has no
-- machine entry, whereas the second request reaches a block after dispatch.
example : (request 0 0).start primitives = .error linkFailure ∧
    ¬ (request 0 0).Returns primitives ∧ ¬ (request 0 0).Blocks primitives ∧
    ¬ (request 0 0).Diverges primitives :=
  ⟨start_error_iff.mpr (linkBlocked 0), outcomes.link_block_exclusive ⟨_, linkBlocked 0⟩⟩

private def blockedConfig : Config machine Nat [number] :=
  ⟨.eval (invokeSite 0).job (saved.push .halt), 25⟩

example : (request 2 0).start primitives = .ok (source 0) ∧
    Relation.ReflTransGen (Step primitives) (source 0) blockedConfig ∧ blockedConfig.Blocked primitives :=
  ⟨started 0, invokedBlock.steps .halt, invokedBlock.blocks .halt⟩

example : (request 2 0).Blocks primitives ∧ ¬ (request 2 0).LinkBlocks primitives := by
  have blocked : (request 2 0).Blocks primitives :=
    blocks_iff_machine.mpr ⟨_, started 0, _, invokedBlock.steps .halt, invokedBlock.blocks .halt⟩
  exact ⟨blocked, fun failed => (outcomes.link_block_exclusive failed).2.1 blocked⟩

-- Partial initialization publishes payload 12. The fixture's total initializer
-- would publish 102. The call output observes the actual payload and store 25.
example : (request 2 1).start primitives =
      .ok ⟨Continuation.start (.call callee (numberValue 1)), 25⟩ ∧
    Relation.ReflTransGen (Step primitives) (source 1) ⟨.returned (numberValue 38) .halt, 27⟩ :=
  ⟨started 1, invokedReturn.steps .halt⟩

example : (request 2 1).Returns primitives :=
  returns_iff_machine.mpr ⟨_, started 1, numberValue 38, 27, invokedReturn.steps .halt⟩

example : Executable.link actions 73 graph (numberValue 2) 20 = .linked published 25 :=
  Executable.link_iff.mpr (linked 1)

example : Executable.run actions 0 73 graph (numberValue 0) .head (numberValue 0) 20 = .error linkFailure :=
  (Executable.run_error_iff (request 0 0) actions 0).mpr (linkBlocked 0)

section ExecutableModule

private abbrev moduleInputs : Ports T := [number, number]
private abbrev moduleOutputs : Ports T := [fn.port, fn.port]
private abbrev moduleItems : List (Ports T) := [[global], [global], [fn.port], [fn.port]]

private def seedDelta : DeltaTerm Op moduleInputs [] (.data ()) :=
  ⟨[number], .cons (.arg .head) .nil, [[number]], initTerm⟩

private def guardDelta : DeltaTerm Op moduleInputs [[global]] (.data ()) :=
  ⟨[number], .cons (.arg (.tail .head)) .nil, [[number]], initTerm⟩

private def exportLambda : LambdaTerm Op moduleInputs [[global], [global]] fn :=
  ⟨[global], .cons (.output (0 : Fin 2) .head) .nil, [[number]], body⟩

private def exportGroup : PhiTerm Op moduleInputs [[global], [global], [fn.port]] [fn] :=
  ⟨[global], .cons (.output (0 : Fin 3) .head) .nil,
    .cons ⟨[global], .cons (.arg .head) .nil, [[number]], body⟩ .nil⟩

private def moduleGraph : Omega Op moduleInputs moduleOutputs moduleItems :=
  OmegaTerm.toGraph ⟨.bind (.delta seedDelta) <| .bind (.delta guardDelta) <|
    .bind (.lambda exportLambda) <| .bind (.phi exportGroup) <|
    .ret (.cons (.output (2 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil))⟩

private def runModule (fuel guard : Nat) (port : Port moduleOutputs fn.port) :
    Except (Failure machine Nat) (Continuation.Partial.Executable.Observation machine Nat [number]) :=
  Executable.run actions fuel 73 moduleGraph (.cons (.data (2 : Nat)) (numberValue guard)) port (numberValue 1) 20

-- Both exports consume the first initialized global, with payload 12.
-- Each invocation starts at store 30 after the two successful initializers.
example : runModule 64 3 .head = .ok (.returned (numberValue 43) 32) := by cbv

example : runModule 64 3 (.tail .head) = .ok (.returned (numberValue 43) 32) := by cbv

private def suspensionStore :
    Except (Failure machine Nat) (Continuation.Partial.Executable.Observation machine Nat [number]) → Option Nat
  | .ok (.suspended config) => some config.store
  | _ => none

example : suspensionStore (runModule 0 3 (.tail .head)) = some 30 := by cbv

private def initializerOperand {ins outs : Ports T} : Op ins outs → Tuple machine.Val ins → Option Nat
  | .initialize, .cons (.data n) .nil => some n
  | .observe, _ => none

private def failureDetails :
    Except (Failure machine Nat) (Continuation.Partial.Executable.Observation machine Nat [number]) →
    Option (Nat × Nat × Nat × Nat)
  | .error failure => (initializerOperand failure.site.opcode failure.site.input).map
      (fun n => (failure.unitId, failure.vertex, n, failure.store))
  | .ok _ => none

-- The second initializer fails after the seed changed the store.
-- This is a link-time error even with zero invocation microsteps.
example : failureDetails (runModule 0 0 (.tail .head)) = some (73, 1, 0, 25) := by cbv

end ExecutableModule

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Tests
