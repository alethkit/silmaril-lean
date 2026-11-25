module

import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Tests

open OrderedRuntime
open Structured (Instruction Values)
open NestedTheta (Node Term)

private abbrev Ty := Structured.Ty Unit
private abbrev dataPorts : Ports Ty := [.value ()]
private abbrev bodyPorts : Ports Ty := Theta.BodyResults dataPorts
private abbrev args : Ports Ty := .control 2 :: dataPorts

private inductive Effect : Ports Ty → Ports Ty → Type where
  | bump : Effect dataPorts bodyPorts
  | inspect : Effect dataPorts bodyPorts
  | addHundred : Effect dataPorts dataPorts

private abbrev Pure : Dialect Unit Unit := fun _ _ => Empty
private abbrev Op := Instruction Pure Effect

private def model : Structured.Model Pure Effect (StateM Nat) where
  value _ := Nat
  runPure op _ := nomatch op
  effect
    | .bump, .cons n .nil => StateT.mk fun s =>
      let next := (show Nat from n) + 1
      let tag : Fin 2 := if next % 2 = 1 then 1 else 0
      (.cons ⟨tag⟩ (.cons next .nil), s + 1)
    | .inspect, _ => StateT.mk fun s =>
      let tag : Fin 2 := if s < 3 then 1 else 0
      (.cons ⟨tag⟩ (.cons s .nil), 2 * s + 1)
    | .addHundred, input => StateT.mk fun s => (input, s + 100)

private def data (n : Nat) : Tuple (Values model.value) dataPorts := .cons n .nil
private def input (arm : Fin 2) : Tuple (Values model.value) args := .cons ⟨arm⟩ (data 0)

private def bodyResult (tag : Fin 2) (n : Nat) : Tuple (Values model.value) bodyPorts :=
  .cons ⟨tag⟩ (data n)

private def effectNode {entry out : Ports Ty} {past : List (Ports Ty)}
    (op : Effect dataPorts out) (source : Origin entry past (.value ())) : Node Op entry past out :=
  ⟨dataPorts, .base (.simple (.effect op)), .cons source .nil, fun i => i.elim0⟩

private def innerBody : Term Op dataPorts [] [bodyPorts] bodyPorts :=
  .bind (effectNode .bump (.arg .head)) (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def outerBody : Term Op dataPorts [] [dataPorts, bodyPorts] bodyPorts :=
  .bind (thetaVertex [bodyPorts]) (fun _ => innerBody) <|
    .bind (effectNode .inspect (.output (0 : Fin 1) .head)) (fun i => i.elim0)
      (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil)))

private def chargedArm : Term Op dataPorts [] [dataPorts] dataPorts :=
  .bind (effectNode .addHundred (.arg .head)) (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private abbrev choice : Node Op args [] dataPorts :=
  ⟨args, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    Fin.cases [] (fun _ => [dataPorts])⟩

private abbrev outer : Node Op args [dataPorts] dataPorts :=
  ⟨dataPorts, .theta dataPorts, .cons (.output (0 : Fin 1) .head) .nil, fun _ => [dataPorts, bodyPorts]⟩

private def program : Term Op args [] [dataPorts, dataPorts] dataPorts :=
  .bind choice
    (Fin.cases (motive := fun i => Term Op dataPorts [] (choice.childSigs i) dataPorts)
      (.ret (.cons (.arg .head) .nil)) (fun _ => chargedArm)) <|
    .bind outer (fun _ => outerBody) (.ret (.cons (.output (1 : Fin 2) .head) .nil))

private theorem firstBody (s : Nat) :
    exec model outerBody (data 0) PUnit.unit s
      (bodyResult (if s + 1 + 1 < 3 then 1 else 0) (s + 1 + 1), 2 * (s + 1 + 1) + 1) := by
  refine ⟨(data 2, s + 1 + 1), ?_, ?_⟩
  · refine Theta.Iterate.again (next := (data 1, s + 1)) ?_ (Theta.Iterate.stop ?_)
    · exact ⟨(bodyResult 1 1, s + 1), rfl, rfl⟩
    · refine ⟨(bodyResult 0 2, s + 1 + 1), ?_, ?_⟩
      · simp only [kindExec, effectNode, Structured.Model.step, model, Wires.read, data, bodyResult,
          StateT.run, StateT.mk, Tuple.map]
        rfl
      · simp only [exec, Wires.read, Locals.snoc, Tuple.map, bodyResult, tagged, data]
        rfl
  · exact ⟨(bodyResult (if s + 1 + 1 < 3 then 1 else 0) (s + 1 + 1), 2 * (s + 1 + 1) + 1), rfl, rfl⟩

private theorem secondBody :
    exec model outerBody (data 2) PUnit.unit 5 (bodyResult 0 7, 15) := by
  refine ⟨(data 4, 7), ?_, ?_⟩
  · refine Theta.Iterate.again (next := (data 3, 6)) ?_ (Theta.Iterate.stop ?_)
    · exact ⟨(bodyResult 1 3, 6), rfl, rfl⟩
    · exact ⟨(bodyResult 0 4, 7), rfl, rfl⟩
  · exact ⟨(bodyResult 0 7, 15), rfl, rfl⟩

-- Two inner loops advance the state from 0 to 2 and from 5 to 7. Each
-- inspect reads the state left by its inner loop. The charged arm is skipped.
example : observe model program.toGraph (input 0) 0 = Part.some (data 7, 15) := by
  apply (observe_eq_some model _ _ _ _).mpr
  rw [Term.toTerm_toGraph]
  refine ⟨(data 0, 0), rfl, (data 7, 15), ?_, rfl⟩
  exact Theta.Iterate.again (next := (data 2, 5)) (firstBody 0) (.stop secondBody)

-- Selecting the charged arm supplies state 100 to the outer loop. The
-- inspect reads 102 after the inner loop and exits on its first activation.
example : observe model program.toGraph (input 1) 0 = Part.some (data 102, 205) := by
  apply (observe_eq_some model _ _ _ _).mpr
  rw [Term.toTerm_toGraph]
  refine ⟨(data 0, 100), ⟨(data 0, 100), rfl, rfl⟩, (data 102, 205), ?_, rfl⟩
  exact Theta.Iterate.stop (firstBody 100)

end Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Tests
