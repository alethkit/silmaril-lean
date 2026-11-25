module

import Silmaril.SSA.RVSDG.Petri.Thms

namespace Silmaril.SSA.RVSDG.Petri.Tests

open Relation (ReflTransGen)

private abbrev Ty := PortType Unit Unit
private abbrev st : Ty := .state ()
private abbrev val : Ty := .value ()
private abbrev statePorts : Ports Ty := [st]
private abbrev valuePorts : Ports Ty := [val]
private abbrev entryPorts : Ports Ty := [.control 2, st]
private abbrev readPorts : Ports Ty := [st, val, val]
private abbrev resultPorts : Ports Ty := [val, st]
private abbrev sigs : List (Ports Ty) := [statePorts, statePorts, valuePorts, valuePorts, resultPorts]

private inductive Op : Ports Ty → Ports Ty → Type where
  | record (digit : Nat) : Op statePorts statePorts
  | literal (value : Nat) : Op [] valuePorts
  | observe : Op readPorts resultPorts

private def model : Model Op where
  value _ := Nat
  state _ := List Nat
  run
    | .record digit, .cons trace .nil => .cons ((show List Nat from trace) ++ [digit]) .nil
    | .literal n, .nil => .cons n .nil
    | .observe, .cons trace (.cons a (.cons b .nil)) =>
      .cons (List.length trace + (show Nat from a) + (show Nat from b)) (.cons trace .nil)

private def state (trace : List Nat) : Tuple model.Val statePorts := .cons trace .nil
private def value (n : Nat) : Tuple model.Val valuePorts := .cons n .nil
private def answer : Tuple model.Val resultPorts := .cons (21 : Nat) (.cons [1, 12, 13] .nil)

private abbrev record {args : Ports Ty} {past : List (Ports Ty)} (digit : Nat)
    (wire : Origin args past st) : Node Op args past statePorts :=
  ⟨statePorts, .simple (.record digit), .cons wire .nil, fun j => j.elim0⟩

private abbrev literal {args : Ports Ty} {past : List (Ports Ty)} (n : Nat) : Node Op args past valuePorts :=
  ⟨[], .simple (.literal n), .nil, fun j => j.elim0⟩

private abbrev gamma : Node Op entryPorts [statePorts] statePorts :=
  ⟨entryPorts, .gamma 0, .cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil),
    fun _ => [statePorts, statePorts]⟩

private def child (arm : Fin 2) : Term Op statePorts [] [statePorts, statePorts] statePorts :=
  let first : Node Op statePorts [] statePorts := record (10 * arm.val + 2) (.arg .head)
  let second : Node Op statePorts [statePorts] statePorts :=
    record (10 * arm.val + 3) (.output (0 : Fin 1) .head)
  .bind first (fun j => Fin.elim0 (show Fin 0 from j))
    (.bind second (fun j => Fin.elim0 (show Fin 0 from j))
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))

private abbrev observer : Node Op entryPorts [statePorts, statePorts, valuePorts, valuePorts] resultPorts :=
  ⟨readPorts, .simple .observe,
    .cons (.output (1 : Fin 4) .head)
      (.cons (.output (2 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil)),
    fun j => j.elim0⟩

private def term : Term Op entryPorts [] sigs resultPorts :=
  .bind (record 1 (.arg (.tail .head))) (fun j => j.elim0) <|
    .bind gamma child <|
      .bind (literal 9) (fun j => j.elim0) <|
        .bind (literal 5) (fun j => j.elim0) <|
          .bind observer (fun j => j.elim0) <|
            .ret (.cons (.output (4 : Fin 5) .head) (.cons (.output (4 : Fin 5) (.tail .head)) .nil))

private def graph : Graph Op entryPorts [] sigs resultPorts := term.toGraph

private def inputFor (arm : Fin 2) : Tuple model.Val entryPorts := .cons ⟨arm⟩ (state [])
private def input : Tuple model.Val entryPorts := inputFor 1

private abbrev Mark := GraphMarking model graph

private def fourthFired : Mark := (.pending, .pending, .pending, .done (value 5), .pending, PUnit.unit)
private def stateRecorded : Mark := (.done (state [1]), .pending, .pending, .done (value 5), .pending, PUnit.unit)
private def armEntered : Mark :=
  (.done (state [1]), .waiting (1 : Fin 2) (state [1], .pending, .pending, PUnit.unit),
    .pending, .done (value 5), .pending, PUnit.unit)
private def armStarted : Mark :=
  (.done (state [1]), .waiting (1 : Fin 2) (state [1], .done (state [1, 12]), .pending, PUnit.unit),
    .pending, .done (value 5), .pending, PUnit.unit)
private def interleaved : Mark :=
  (.done (state [1]), .waiting (1 : Fin 2) (state [1], .done (state [1, 12]), .pending, PUnit.unit),
    .done (value 9), .done (value 5), .pending, PUnit.unit)
private def armFinished : Mark :=
  (.done (state [1]), .waiting (1 : Fin 2) (state [1], .done (state [1, 12]), .done (state [1, 12, 13]), PUnit.unit),
    .done (value 9), .done (value 5), .pending, PUnit.unit)
private def statePublished : Mark :=
  (.done (state [1]), .done (state [1, 12, 13]), .done (value 9), .done (value 5), .pending, PUnit.unit)
private def done : Mark :=
  (.done (state [1]), .done (state [1, 12, 13]), .done (value 9), .done (value 5), .done answer, PUnit.unit)

-- The unused independent vertex 3 fires first. Vertex 2 fires between the two
-- transitions of the selected child. The consumer reads its published value twice.
private theorem schedule : ReflTransGen (Step model graph input) (initial model graph) done := by
  have h1 : Step model graph input (initial model graph) fourthFired :=
    .later (.later (.later (.primitive rfl rfl)))
  have h2 : Step model graph input fourthFired stateRecorded := .primitive rfl rfl
  have h3 : Step model graph input stateRecorded armEntered := .later (.enter rfl rfl)
  have h4 : Step model graph input armEntered armStarted := .later (.advance (.primitive rfl rfl))
  have h5 : Step model graph input armStarted interleaved := .later (.later (.primitive rfl rfl))
  have h6 : Step model graph input interleaved armFinished := .later (.advance (.later (.primitive rfl rfl)))
  have h7 : Step model graph input armFinished statePublished := .later (.commit rfl)
  have h8 : Step model graph input statePublished done := .later (.later (.later (.later (.primitive rfl rfl))))
  exact (((((((ReflTransGen.single h1).tail h2).tail h3).tail h4).tail h5).tail h6).tail h7).tail h8

example : Finishes model graph input answer := ⟨done, schedule, rfl⟩

example : graph.run model input = answer :=
  (finishes_iff model graph input answer).1 ⟨done, schedule, rfl⟩

private def otherAnswer : Tuple model.Val resultPorts := .cons (21 : Nat) (.cons [1, 2, 3] .nil)

example : Finishes model graph (inputFor 0) otherAnswer :=
  (finishes_iff model graph (inputFor 0) otherAnswer).2 rfl

example : select model gamma.shape (.cons (⟨1⟩ : ULift (Fin 2)) (state [1])) ≠
    some ((0 : Fin 2), state [1]) := by
  intro wrong
  have branch := congrArg (fun option => option.map (fun pair => pair.1.val)) wrong
  cases branch

example : result model graph input armFinished = none := rfl

-- Even when the result wires have their colours, a dead but pending vertex
-- keeps the region from completing.
example : result model graph input
    (.done (state [1]), .done (state [1, 12, 13]), .done (value 9), .pending, .done answer, PUnit.unit) =
    none := rfl

-- While the child is waiting to commit, the consumer cannot read its state output.
example : read observer.inputs input
    (Tuple.map (fun _ => some) (state [1]), absent statePorts,
      Tuple.map (fun _ => some) (value 9), Tuple.map (fun _ => some) (value 5), PUnit.unit) = none := rfl

end Silmaril.SSA.RVSDG.Petri.Tests
