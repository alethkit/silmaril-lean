module

import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Feedback.Regression

open OrderedRuntime
open Structured (Data Opcode Threaded nextRuntime runtimePort withRuntime)
open ExplicitRuntime (EntryChecked)

private abbrev Ty := Structured.Ty Unit
private abbrev val : Ty := .value ()
private abbrev flag : Ty := .control 2
private abbrev carried : Ports Ty := [val, val, val, val]
private abbrev entry : Ports Ty := flag :: carried
private abbrev primitiveResults : Ports Ty := [flag, val]
private abbrev carriedData : Data carried := .value (.value (.value (.value .nil)))
private abbrev entryData : Data entry := .control carriedData
private abbrev bodyData : Data (Theta.BodyResults carried) := .control carriedData
private abbrev valueData : Data ([val] : Ports Ty) := .value .nil
private abbrev primitiveData : Data primitiveResults := .control valueData

private abbrev Pure : Dialect Unit PUnit := fun _ _ => Empty
private inductive Effect : Dialect Unit PUnit where
  | test : Effect [val] primitiveResults

private abbrev Op := Opcode Pure Effect

private def model : Structured.Model Pure Effect (StateM Nat) where
  value _ := Nat
  runPure op _ := nomatch op
  effect
    | .test, .cons predicate .nil => fun token =>
      let current : Nat := predicate
      let decision : Fin 2 := if current = 0 then 0 else 1
      (.cons ⟨decision⟩ (.cons (token + 10 + current) .nil), 2 * token + current + 1)

private abbrev CheckedTerm {ins outs : Ports Ty} (i : Data ins) (o : Data outs)
    (sigs : List (Ports Ty)) :=
  Σ t : Term Op (Threaded ins) [] sigs (Threaded outs), EntryChecked (a := i) (b := o) t

private def bodyResults :
    Wires (Threaded carried) [Threaded primitiveResults] (Theta.BodyResults carried) :=
  let source : Origin (Threaded carried) [Threaded primitiveResults] val := .arg (.tail .head)
  .cons (.output (0 : Fin 1) .head)
    (.cons source (.cons source (.cons (.output (0 : Fin 1) (.tail .head))
      (.cons (.arg (.tail (.tail (.tail .head)))) .nil))))

private def body : CheckedTerm carriedData bodyData [Threaded primitiveResults] :=
  ⟨_, .primitive (.arg (runtimePort carried)) valueData primitiveData (.effect .test)
    (.cons (.arg .head) .nil) (.ret (nextRuntime [] primitiveResults) bodyResults)⟩

private def carriedInputs : Wires (Threaded carried) [] carried :=
  .cons (.arg .head) (.cons (.arg (.tail .head))
    (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil)))

private def carriedResults {args : Ports Ty} : Wires args [Threaded carried] carried :=
  .cons (.output 0 .head) (.cons (.output 0 (.tail .head))
    (.cons (.output 0 (.tail (.tail .head))) (.cons (.output 0 (.tail (.tail (.tail .head)))) .nil)))

private def arms (tag : Fin 2) :
    CheckedTerm carriedData carriedData (Fin.cases [] (fun _ => [Threaded carried]) tag) :=
  Fin.cases
    ⟨_, .ret (.arg (runtimePort carried)) carriedInputs⟩
    (fun _ => ⟨_, .theta (.arg (runtimePort carried)) carriedData carriedInputs
      [Threaded primitiveResults] (children := fun _ => body.1) (fun _ => body.2)
      (.ret (nextRuntime [] carried) carriedResults)⟩) tag

private def captureWires : Wires (Threaded entry) [] carried :=
  carriedInputs.map fun _ wire => match wire with
    | .arg p => .arg (.tail p)
    | .output i _ => i.elim0

private def program : CheckedTerm entryData carriedData [Threaded carried] :=
  ⟨_, .gamma 0 (.arg .head) (.arg (runtimePort entry)) carriedData carriedData captureWires
    (Fin.cases [] (fun _ => [Threaded carried]))
    (children := fun tag => (arms tag).1) (fun tag => (arms tag).2)
    (.ret (nextRuntime [] carried) carriedResults)⟩

private def graph := program.1.toGraph
private def payloadOnly : Demand := (· == 2)
private def stateOnly : Demand := fun _ => false
private def analyzeBody (demand : Demand) : List Address := (body.1.demandPlan demand).live

-- The decision and state read the first carried value. The second value
-- only becomes live when the first input is demanded at the next restart.
example : step stateOnly analyzeBody (∅ : Mask 5) = {0, 4} := by decide
example : step payloadOnly analyzeBody (∅ : Mask 5) = {0, 4} := by decide
example : step stateOnly analyzeBody ({0, 4} : Mask 5) = {0, 1, 4} := by decide
example : body.1.feedbackLive stateOnly = ({0, 1, 4} : Mask 5) := by decide
example : body.1.feedbackLive payloadOnly = ({0, 1, 4} : Mask 5) := by decide

example : graph.liveAt 0 = [.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5] := by decide
example : graph.demandLiveIn stateOnly = [.arg 0, .arg 1, .arg 2, .arg 5] := by decide
example : graph.demandLiveIn payloadOnly = [.arg 0, .arg 1, .arg 2, .arg 3, .arg 5] := by decide

private def point (predicate source payload dead token : Nat) :
    Tuple model.toRVSDG.Val (Threaded carried) :=
  withRuntime token (.cons predicate (.cons source (.cons payload (.cons dead .nil))))

private def input (source dead : Nat) : Tuple model.toRVSDG.Val (Threaded entry) :=
  .cons ⟨1⟩ (point 1 source 7 dead 0)

private theorem agree_dead (demand : Demand) (absent : Address.arg 4 ∉ graph.demandLiveIn demand)
    (source : Nat) : graph.AgreesOnDemandInputs demand (input source 9) (input source 90) := by
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
        | head => rfl
        | tail p =>
          cases p with
          | head => exact False.elim (absent listed)
          | tail p =>
            cases p with
            | head => rfl
            | tail p => nomatch p

-- The selected arm takes one feedback edge, exits on its second completion,
-- and returns payload 12 with token 5. The undemanded carried value can change.
example : graph.run model.toRVSDG 2 (input 0 90) = some (point 0 0 12 90 5) := rfl
example : graph.ReturnsDemand model.toRVSDG payloadOnly (input 0 90) (point 0 0 12 9 5) :=
  (graph.returnsDemand_iff model.toRVSDG payloadOnly _ _
    (agree_dead payloadOnly (by decide) 0) _).1
    ⟨_, ⟨2, rfl⟩, fun _ _ => rfl⟩

private def stream (dead : Nat) : Nat → Tuple model.toRVSDG.Val (Threaded carried)
  | 0 => point 1 1 7 dead 0
  | n + 1 =>
    let token : Nat := (stream dead n).get (runtimePort carried)
    point 1 1 (token + 11) dead (2 * token + 2)

private theorem step_stream (fuel dead n : Nat) :
    body.1.run model.toRVSDG fuel (stream dead n) =
      some (Theta.bodyResult model.toRVSDG true (stream dead (n + 1))) := by
  cases n <;> rfl

-- Productive non-return consists of actual completed body executions.
example (dead : Nat) : Theta.Repeats (fun before again after =>
    body.1.run model.toRVSDG 0 before = some (Theta.bodyResult model.toRVSDG again after))
    (point 1 1 7 dead 0) :=
  ⟨stream dead, rfl, step_stream 0 dead⟩

private def keepsGoing (tag : model.toRVSDG.Val (.control 2)) : Bool := tag.down.val == 1

private theorem stream_no_return (bodyFuel fuel dead n : Nat) :
    iterate (body.1.run model.toRVSDG bodyFuel) keepsGoing fuel (stream dead n) = none := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    change (match body.1.run model.toRVSDG bodyFuel (stream dead n) with
      | none => none
      | some (.cons tag next) =>
        if keepsGoing tag then iterate (body.1.run model.toRVSDG bodyFuel) keepsGoing fuel next
        else some next) = none
    rw [step_stream]
    exact ih (n + 1)

private theorem graph_no_return (fuel : Nat) : graph.run model.toRVSDG fuel (input 1 9) = none := by
  refine (graph.run_toTerm model.toRVSDG fuel (input 1 9)).symm.trans ?_
  change program.1.toGraph.toTerm.run model.toRVSDG fuel (input 1 9) = none
  rw [Term.toTerm_toGraph]
  change ((iterate (body.1.run model.toRVSDG fuel) keepsGoing fuel (stream 9 0)).bind _).bind _ = none
  rw [stream_no_return]
  rfl

-- Changing the feedback-only source from zero to one changes termination.
-- Changing the dead value preserves non-return even with empty data demand.
example : ¬ ∃ out, graph.Returns model.toRVSDG (input 1 90) out := by
  rw [← graph.hasFiniteReturn_iff_of_demand model.toRVSDG stateOnly _ _
    (agree_dead stateOnly (by decide) 1)]
  rintro ⟨out, fuel, returned⟩
  rw [graph_no_return] at returned
  contradiction

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Feedback.Regression
