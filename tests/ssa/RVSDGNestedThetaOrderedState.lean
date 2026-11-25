module

import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms

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

open Structured (Data Opcode Threaded decode nextRuntime runtimePort)

private abbrev dataOnly : Data dataPorts := .value .nil
private abbrev bodyData : Data bodyPorts := .control dataOnly
private abbrev entryData : Data args := .control dataOnly

private abbrev ExplicitEntry {entry outs : Ports Ty} (a : Data entry) (b : Data outs)
    (sigs : List (Ports Ty)) :=
  Σ t : Term (Opcode Pure Effect) (Threaded entry) [] sigs (Threaded outs),
    ExplicitRuntime.EntryChecked (a := a) (b := b) t

private def explicitBump : ExplicitEntry dataOnly bodyData [Threaded bodyPorts] :=
  ⟨_, .primitive (.arg (runtimePort dataPorts)) dataOnly bodyData (.effect .bump) (.cons (.arg .head) .nil)
    (.ret (nextRuntime [] bodyPorts)
      (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

private def explicitOuterBody : ExplicitEntry dataOnly bodyData [Threaded dataPorts, Threaded bodyPorts] :=
  ⟨_, .theta (.arg (runtimePort dataPorts)) dataOnly (.cons (.arg .head) .nil) [Threaded bodyPorts]
    (children := fun _ => explicitBump.1) (fun _ => explicitBump.2)
    (.primitive (nextRuntime [] dataPorts) dataOnly bodyData (.effect .inspect)
      (.cons (.output (0 : Fin 1) .head) .nil)
      (.ret (nextRuntime [Threaded dataPorts] bodyPorts)
        (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))⟩

private def explicitArms (tag : Fin 2) :
    ExplicitEntry dataOnly dataOnly (Fin.cases [] (fun _ => [Threaded dataPorts]) tag) :=
  Fin.cases
    ⟨_, .ret (.arg (runtimePort dataPorts)) (.cons (.arg .head) .nil)⟩
    (fun _ => ⟨_, .primitive (.arg (runtimePort dataPorts)) dataOnly dataOnly (.effect .addHundred)
      (.cons (.arg .head) .nil) (.ret (nextRuntime [] dataPorts) (.cons (.output (0 : Fin 1) .head) .nil))⟩) tag

private def explicitProgram : ExplicitEntry entryData dataOnly [Threaded dataPorts, Threaded dataPorts] :=
  ⟨_, .gamma 0 (.arg .head) (.arg (runtimePort args)) dataOnly dataOnly
    (.cons (.arg (.tail .head)) .nil) (Fin.cases [] (fun _ => [Threaded dataPorts]))
    (children := fun j => (explicitArms j).1) (fun j => (explicitArms j).2)
    (.theta (nextRuntime [] dataPorts) dataOnly (.cons (.output (0 : Fin 1) .head) .nil)
      [Threaded dataPorts, Threaded bodyPorts]
      (children := fun _ => explicitOuterBody.1) (fun _ => explicitOuterBody.2)
      (.ret (nextRuntime [Threaded dataPorts] dataPorts) (.cons (.output (1 : Fin 2) .head) .nil)))⟩

-- The bounded, explicit graph evaluator supplies the finite observation.
-- The erased computation skips the unselected effect, and the two outer
-- activations inspect the actual state returned by the inner θ.
example : ExplicitRuntime.observe model explicitProgram.1.toGraph explicitProgram.2.collect (decode (input 0, 0)) =
    Part.some (Structured.withRuntime PUnit.unit (data 7), 15) :=
  (ExplicitRuntime.observe_eq_some model _ explicitProgram.2.collect _ (decode (data 7, 15))).mpr ⟨2, rfl⟩

-- Selecting the other arm adds 100 before entering the loop, so the first
-- outer activation returns payload 102 and token 205.
example : ExplicitRuntime.observe model explicitProgram.1.toGraph explicitProgram.2.collect (decode (input 1, 0)) =
    Part.some (Structured.withRuntime PUnit.unit (data 102), 205) :=
  (ExplicitRuntime.observe_eq_some model _ explicitProgram.2.collect _ (decode (data 102, 205))).mpr ⟨2, rfl⟩

end Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Tests
