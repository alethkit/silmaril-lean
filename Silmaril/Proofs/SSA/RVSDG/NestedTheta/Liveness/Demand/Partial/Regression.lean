module

import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Thms
import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Regression

open OrderedRuntime
open Structured (Data Opcode Values Threaded nextRuntime runtimePort withRuntime)
open ExplicitRuntime (EntryChecked ThreadedOp)
open ExplicitRuntime.Partial (Observation abnormal attempt primitive_mem_iff wireModel)

private abbrev Ty := Structured.Ty Unit
private abbrev val : Ty := .value ()
private abbrev flag : Ty := .control 2
private abbrev scalar : Ports Ty := [val]
private abbrev carry : Ports Ty := [val, val, val]
private abbrev entry : Ports Ty := flag :: carry
private abbrev advanceResults : Ports Ty := [flag, val]
private abbrev scalarData : Data scalar := .value .nil
private abbrev carryData : Data carry := .value (.value scalarData)
private abbrev entryData : Data entry := .control carryData
private abbrev advanceData : Data advanceResults := .control scalarData
private abbrev bodyData : Data (Theta.BodyResults carry) := .control carryData

private abbrev Pure : Dialect Unit PUnit := fun _ _ => Empty
private inductive Effect : Dialect Unit PUnit where
  | probe : Effect scalar scalar
  | advance : Effect scalar advanceResults

private def again (counter : Nat) : Bool := if counter = 1 then false else true

private def model : ExplicitRuntime.Partial.Model Pure Effect Nat where
  value _ := Nat
  runPure op _ := nomatch op
  effect
    | .probe, .cons operand .nil => fun token =>
      let operand : Nat := operand
      if operand = 7 ∧ token = 5 then Part.none
      else Part.some (.cons (operand + 100) .nil, token + 1)
    | .advance, .cons counter .nil => fun token =>
      let counter : Nat := counter
      let decision : Fin 2 := if again counter then 1 else 0
      Part.some (.cons ⟨decision⟩ (.cons (counter + 1) .nil), token + 2)

private abbrev Op := Opcode Pure Effect
private abbrev VM := (wireModel model)
private abbrev CheckedTerm {ins outs : Ports Ty} (i : Data ins) (o : Data outs)
    (sigs : List (Ports Ty)) :=
  Σ t : Term Op (Threaded ins) [] sigs (Threaded outs), EntryChecked (a := i) (b := o) t

private def bodyResults : Wires (Threaded carry) [Threaded scalar, Threaded advanceResults]
    (Theta.BodyResults carry) :=
  .cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head))
    (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)))

-- The probe's data result has no readers. Its operand and runtime still
-- participate in the actual attempt, and success passes its updated token on.
private def body : CheckedTerm carryData bodyData [Threaded scalar, Threaded advanceResults] :=
  ⟨_, .primitive (.arg (runtimePort carry)) scalarData scalarData (.effect .probe)
    (.cons (.arg (.tail .head)) .nil)
    (.primitive (nextRuntime [] scalar) scalarData advanceData (.effect .advance)
      (.cons (.arg .head) .nil) (.ret (nextRuntime [Threaded scalar] advanceResults) bodyResults))⟩

private def carryInputs : Wires (Threaded carry) [] carry :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))

private def carryResults {args : Ports Ty} : Wires args [Threaded carry] carry :=
  .cons (.output 0 .head) (.cons (.output 0 (.tail .head)) (.cons (.output 0 (.tail (.tail .head))) .nil))

private def arms (tag : Fin 2) :
    CheckedTerm carryData carryData (Fin.cases [Threaded carry] (fun _ => []) tag) :=
  Fin.cases
    ⟨_, .theta (.arg (runtimePort carry)) carryData carryInputs
      [Threaded scalar, Threaded advanceResults] (children := fun _ => body.1) (fun _ => body.2)
      (.ret (nextRuntime [] carry) carryResults)⟩
    (fun _ => ⟨_, .ret (.arg (runtimePort carry)) carryInputs⟩) tag

private def captures : Wires (Threaded entry) [] carry :=
  carryInputs.map fun _ wire => match wire with
    | .arg p => .arg (.tail p)
    | .output i _ => i.elim0

private def program : CheckedTerm entryData carryData [Threaded carry] :=
  ⟨_, .gamma 0 (.arg .head) (.arg (runtimePort entry)) carryData carryData captures
    (Fin.cases [Threaded carry] (fun _ => []))
    (children := fun j => (arms j).1) (fun j => (arms j).2)
    (.ret (nextRuntime [] carry) carryResults)⟩

private abbrev graph := program.1.toGraph
private def stateOnly : Demand := fun _ => false
private def counterOnly : Demand := (· == 0)

example : graph.demandLiveIn stateOnly = [.arg 0, .arg 1, .arg 2, .arg 4] := by decide
example : graph.demandLiveIn counterOnly = [.arg 0, .arg 1, .arg 2, .arg 4] := by decide
example : Address.arg 2 ∈ (graph.demandLiveness stateOnly).mayOut 0 :=
  (graph.mem_demandLiveIn_iff stateOnly _).1 (by decide)

private def point (counter operand dead token : Nat) : Tuple VM.Val (Threaded carry) :=
  withRuntime token (.cons counter (.cons operand (.cons dead .nil)))

private def input (counter operand dead : Nat) : Tuple VM.Val (Threaded entry) :=
  .cons ⟨0⟩ (point counter operand dead 2)

private theorem inputs_agree (demand : Demand) (absent : Address.arg 3 ∉ graph.demandLiveIn demand)
    (counter operand : Nat) :
    graph.AgreesOnDemandInputs demand (input counter operand 9) (input counter operand 90) := by
  intro ty p live
  have listed := (graph.mem_demandLiveIn_iff demand _).2 live
  cases p with
  | head => rfl
  | tail p =>
    cases p with
    | head => rfl
    | tail p =>
      cases p with
      | head => rfl
      | tail p =>
        cases p with
        | head => exact False.elim (absent listed)
        | tail p =>
          cases p with
          | head => rfl
          | tail p => nomatch p

private def value (n : Nat) : Tuple (Values model.value) scalar := .cons n .nil
private def wiredValue (n token : Nat) : Tuple VM.Val (Threaded scalar) :=
  withRuntime token (.cons n .nil)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem completes (counter operand dead token : Nat)
    (probe : (model.effect .probe (value operand)).run token =
      Part.some (value (operand + 100), token + 1)) :
    NestedTheta.Partial.exec VM body.1 (point counter operand dead token) PUnit.unit
      (NestedTheta.Partial.tagged VM (again counter) (point (counter + 1) operand dead (token + 3))) := by
  let data : Tuple VM.Val advanceResults :=
    .cons ⟨if again counter then 1 else 0⟩ (.cons (counter + 1) .nil)
  let advanceOutput : Tuple VM.Val (Threaded advanceResults) := withRuntime (token + 3) data
  refine ⟨wiredValue (operand + 100) (token + 1), ?_,
    advanceOutput, ?_, ?_⟩
  · change wiredValue (operand + 100) (token + 1) ∈
      VM.primitive (.ordered scalarData scalarData (.effect .probe)) (wiredValue operand token)
    rw [primitive_mem_iff]
    change (value (operand + 100), token + 1) ∈ (model.effect .probe (value operand)).run token
    rw [probe]
    exact Part.mem_some _
  · change advanceOutput ∈
      VM.primitive (.ordered scalarData advanceData (.effect .advance)) (wiredValue counter (token + 1))
    rw [primitive_mem_iff]
    exact Part.mem_some _
  · rfl

private def blocked : Observation model :=
  .blocked ⟨[(0, 0), (0, 0)], 0, Threaded scalar, Threaded scalar, .op .probe,
    withRuntime PUnit.unit (value 7), 5⟩

private theorem blocks : abnormal model graph (input 0 7 9) blocked := by
  rw [abnormal, Term.toTerm_toGraph]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  refine ⟨point 1 7 9 5, .single ?_, Or.inl ⟨?_, rfl⟩⟩
  · exact completes 0 7 9 2 rfl
  · change ¬ False
    exact id

-- The second probe attempts operand 7 at token 5 in the same nested
-- γ arm and θ body. The unrelated carried value may change.
private theorem blocks_changed : abnormal model graph (input 0 7 90) blocked :=
  (abnormal_iff_of_live model graph stateOnly _ _
    (inputs_agree stateOnly (by decide) 0 7) blocked).1 blocks

example : ¬ abnormal model graph (input 0 7 90) .diverges := by
  intro infinite
  have sameBlock :=
    (ExplicitRuntime.Partial.abnormal_iff model graph program.2.collect _ blocked).1 blocks_changed
  have divergence :=
    (ExplicitRuntime.Partial.abnormal_iff model graph program.2.collect _ .diverges).1 infinite
  cases OrderedState.Partial.abnormal_unique _ _ _ _ sameBlock divergence

private theorem returns :
    NestedTheta.Partial.returns VM graph (input 0 8 9) (point 2 8 9 8) := by
  rw [NestedTheta.Partial.returns, Term.toTerm_toGraph]
  refine ⟨point 2 8 9 8, ⟨point 2 8 9 8, ?_, rfl⟩, rfl⟩
  exact .again (next := point 1 8 9 5) (completes 0 8 9 2 rfl) (.stop (completes 1 8 9 5 rfl))

example : ReturnsDemand model graph counterOnly (input 0 8 90) (point 2 0 0 8) :=
  (returnsDemand_iff model graph counterOnly _ _
    (inputs_agree counterOnly (by decide) 0 8) _).1
    ⟨_, returns, by
      intro ty p live
      cases p with
      | head => rfl
      | tail p =>
        cases p with
        | head => contradiction
        | tail p =>
          cases p with
          | head => contradiction
          | tail p =>
            cases p with
            | head => rfl
            | tail p => nomatch p⟩

private theorem keeps_restarting : abnormal model graph (input 2 8 9) .diverges := by
  rw [abnormal, Term.toTerm_toGraph]
  apply Or.inl
  apply Or.inl
  apply Or.inr
  refine ⟨rfl, fun n => point (2 + n) 8 9 (2 + 3 * n), rfl, ?_⟩
  intro n
  simp only [Nat.mul_succ, ← Nat.add_assoc]
  have keepsGoing : again (2 + n) = true := by simp [again, show 2 + n ≠ 1 by omega]
  simpa only [keepsGoing] using completes (2 + n) 8 9 (2 + 3 * n) rfl

example : abnormal model graph (input 2 8 90) .diverges :=
  (abnormal_iff_of_live model graph stateOnly _ _
    (inputs_agree stateOnly (by decide) 2 8) .diverges).1 keeps_restarting

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Regression
