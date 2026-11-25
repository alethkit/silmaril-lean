module

import Silmaril.SSA.RVSDG.Thms

namespace Silmaril.SSA.RVSDG.Tests

private abbrev Ty := PortType Unit Unit
private abbrev stateTy : Ty := .state ()
private abbrev valueTy : Ty := .value ()
private abbrev statePorts : Ports Ty := [stateTy]
private abbrev entryPorts : Ports Ty := [.control 3, stateTy]
private abbrev readPorts : Ports Ty := [valueTy, stateTy]
private abbrev resultPorts : Ports Ty := [valueTy, stateTy, valueTy]
private abbrev sigs : List (Ports Ty) := [statePorts, statePorts, readPorts]

private inductive Op : Ports Ty → Ports Ty → Type where
  | record (digit : Nat) : Op statePorts statePorts
  | read : Op statePorts readPorts

private def model : Model Op where
  value _ := Nat
  state _ := List Nat
  run
    | .record digit, .cons trace .nil => .cons ((show List Nat from trace) ++ [digit]) .nil
    | .read, .cons trace .nil => .cons (List.length trace) (.cons trace .nil)

private def pass : Graph Op statePorts [] [] statePorts :=
  .region (fun i => i.elim0) (fun i => i.elim0) (.cons (.arg .head) .nil)

private def recordArm (digit : Nat) : Graph Op statePorts [] [statePorts] statePorts :=
  .region (Fin.cases
    ⟨statePorts, .simple (.record digit), .cons (.arg .head) .nil, fun j => j.elim0⟩
    (fun i => i.elim0))
    (Fin.cases (fun j => j.elim0) (fun i => i.elim0))
    (.cons (.output (0 : Fin 1) .head) .nil)

private def nodes : Nodes Op entryPorts [] sigs :=
  Fin.cases
    ⟨statePorts, .simple (.record 1), .cons (.arg (.tail .head)) .nil, fun j => j.elim0⟩
    (Fin.cases
      ⟨entryPorts, .gamma 1, .cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil),
        Fin.cases [] (fun _ => [statePorts])⟩
      (Fin.cases
        ⟨statePorts, .simple .read, .cons (.output (1 : Fin 2) .head) .nil, fun j => j.elim0⟩
        (fun i => i.elim0)))

-- This graph is built directly as a table. The state from record feeds gamma and
-- the merged state feeds read. The read node's value has two users in the results.
private def graph : Graph Op entryPorts [] sigs resultPorts :=
  .region nodes
    (Fin.cases (fun j => j.elim0)
      (Fin.cases (Fin.cases pass (fun j => recordArm (j.val + 2)))
        (Fin.cases (fun j => j.elim0) (fun i => i.elim0))))
    (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) (.cons (.output (2 : Fin 3) .head) .nil)))

private def entry (choice : Fin 3) : Tuple model.Val entryPorts :=
  .cons ⟨choice⟩ (.cons [] .nil)

private def observation (trace : List Nat) : Tuple model.Val resultPorts :=
  .cons trace.length (.cons trace (.cons trace.length .nil))

example : graph.run model (entry 0) = observation [1] := rfl
example : graph.run model (entry 1) = observation [1, 2] := rfl
example : graph.run model (entry 2) = observation [1, 3] := rfl
example : graph.toTerm.run model (entry 2) = observation [1, 3] := rfl
example : graph.toTerm.toGraph = graph := Graph.toGraph_toTerm graph

private def term : Term Op statePorts [] [statePorts] statePorts :=
  .bind ⟨statePorts, .simple (.record 7), .cons (.arg .head) .nil, fun j => j.elim0⟩
    (fun j => j.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def stateTuple (trace : List Nat) : Tuple model.Val statePorts := .cons trace .nil

example : term.toGraph.run model (stateTuple [6]) = stateTuple [6, 7] := rfl
example : term.toGraph.toTerm = term := Term.toTerm_toGraph term

example : ((graph.nodes 2).inputs.get .head).producer = some 1 := rfl

-- An empty prefix rules out all producer vertices, and a state argument cannot supply a value.
example (origin : Origin statePorts [] valueTy) : False := by
  cases origin with
  | arg port => cases port with | tail port => cases port
  | output node _ => exact node.elim0

end Silmaril.SSA.RVSDG.Tests
