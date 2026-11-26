module

import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Regression

open OrderedRuntime
open Structured (Data Opcode RuntimeValues Threaded nextRuntime runtimePort withRuntime)
open ExplicitRuntime (EntryChecked)

private abbrev Ty := Structured.Ty Unit
private abbrev val : Ty := .value ()
private abbrev flag : Ty := .control 2
private abbrev carried : Ports Ty := [val, flag]
private abbrev captures : Ports Ty := [val, flag, val, val]
private abbrev entry : Ports Ty := flag :: captures
private abbrev results : Ports Ty := [val, val]
private abbrev stepResults : Ports Ty := Theta.BodyResults carried

private abbrev carriedData : Data carried := .value (.control .nil)
private abbrev captureData : Data captures := .value (.control (.value (.value .nil)))
private abbrev resultData : Data results := .value (.value .nil)
private abbrev stepData : Data stepResults := .control carriedData
private abbrev entryData : Data entry := .control captureData

private abbrev Pure : Dialect Unit PUnit := fun _ _ => Empty
private inductive Effect : Dialect Unit PUnit where
  | advance : Effect carried stepResults

private abbrev Op := Opcode Pure Effect

private def model : Structured.Model Pure Effect (StateM Nat) where
  value _ := Nat
  runPure op _ := nomatch op
  effect
    | .advance, .cons payload (.cons mode .nil) => fun token =>
      let next := (show Nat from payload) + 1
      let tag : Fin 2 := if mode.down.val = 1 ∨ next < 4 then 1 else 0
      (.cons ⟨tag⟩ (.cons next (.cons mode .nil)), 2 * token + next)

private abbrev CheckedTerm {ins outs : Ports Ty} (i : Data ins) (o : Data outs)
    (sigs : List (Ports Ty)) :=
  Σ t : Term Op (Threaded ins) [] sigs (Threaded outs), EntryChecked (a := i) (b := o) t

private def body : CheckedTerm carriedData stepData [Threaded stepResults] :=
  ⟨_, .primitive (.arg (runtimePort carried)) carriedData stepData (.effect .advance)
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.ret (nextRuntime [] stepResults) (.cons (.output (0 : Fin 1) .head)
      (.cons (.output (0 : Fin 1) (.tail .head)) (.cons (.output (0 : Fin 1) (.tail (.tail .head))) .nil))))⟩

private def arms (tag : Fin 2) :
    CheckedTerm captureData resultData (Fin.cases [] (fun _ => [Threaded carried]) tag) :=
  Fin.cases
    ⟨_, .ret (.arg (runtimePort captures))
      (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil))⟩
    (fun _ => ⟨_, .theta (.arg (runtimePort captures)) carriedData
      (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
      [Threaded stepResults] (children := fun _ => body.1) (fun _ => body.2)
      (.ret (nextRuntime [] carried)
        (.cons (.output (0 : Fin 1) .head) (.cons (.arg (.tail (.tail .head))) .nil)))⟩) tag

private def captureWires : Wires (Threaded entry) [] captures :=
  .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head)))
    (.cons (.arg (.tail (.tail (.tail .head))))
      (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)))

private def program : CheckedTerm entryData resultData [Threaded results] :=
  ⟨_, .gamma 0 (.arg .head) (.arg (runtimePort entry)) captureData resultData captureWires
    (Fin.cases [] (fun _ => [Threaded carried]))
    (children := fun tag => (arms tag).1) (fun tag => (arms tag).2)
    (.ret (nextRuntime [] results)
      (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

private def graph := program.1.toGraph
private def firstResult : Demand := (· == 0)
private def stateOnly : Demand := fun _ => false

private def input (tag mode : Fin 2) (spare unused token : Nat) :
    Tuple (RuntimeValues model.value Nat) (Threaded entry) :=
  withRuntime token (.cons ⟨tag⟩ (.cons (2 : Nat) (.cons ⟨mode⟩ (.cons spare (.cons unused .nil)))))

private def result (payload spare token : Nat) :
    Tuple (RuntimeValues model.value Nat) (Threaded results) :=
  withRuntime token (.cons payload (.cons spare .nil))

-- The old rule keeps both extra captures. Demand for only the first result
-- drops the forwarded spare and the unused capture. Full demand keeps the spare.
example : graph.liveAt 0 = [.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5] := by decide
example : graph.demandLiveIn firstResult = [.arg 0, .arg 1, .arg 2, .arg 5] := by decide
example : graph.demandLiveIn (fun _ => true) = [.arg 0, .arg 1, .arg 2, .arg 3, .arg 5] := by decide
example : graph.demandLiveIn stateOnly = [.arg 0, .arg 1, .arg 2, .arg 5] := by decide

private theorem captures_agree (demand : Demand)
    (spareDead : Address.arg 3 ∉ graph.demandLiveIn demand)
    (unusedDead : Address.arg 4 ∉ graph.demandLiveIn demand)
    (mode : Fin 2) :
    graph.AgreesOnDemandInputs demand (input 1 mode 7 9 0) (input 1 mode 70 90 0) := by
  intro ty port live
  have listed := (graph.mem_demandLiveIn_iff demand _).2 live
  cases port with
  | head => rfl
  | tail port =>
    cases port with
    | head => rfl
    | tail port =>
      cases port with
      | head => rfl
      | tail port =>
        cases port with
        | head => exact False.elim (spareDead listed)
        | tail port =>
          cases port with
          | head => exact False.elim (unusedDead listed)
          | tail port =>
            cases port with
            | head => rfl
            | tail port => nomatch port

-- The full tuple changes at port one. The shared agreement proof preserves
-- the requested payload 4 and exact token 10 after two effectful iterations.
example : graph.run model.toRVSDG 2 (input 1 0 70 90 0) = some (result 4 70 10) := rfl
example : graph.ReturnsDemand model.toRVSDG firstResult (input 1 0 70 90 0) (result 4 7 10) :=
  (graph.returnsDemand_iff model.toRVSDG firstResult _ _
    (captures_agree firstResult (by decide) (by decide) 0) _).1
    ⟨result 4 7 10, ⟨2, rfl⟩, fun _ _ => rfl⟩

-- The return depends on the incoming token, and the selector can bypass the loop.
example : graph.run model.toRVSDG 2 (input 1 0 7 9 1) = some (result 4 7 14) := rfl
example : graph.run model.toRVSDG 0 (input 0 1 7 9 0) = some (result 2 7 0) := rfl

private def carriedInput (payload token : Nat) :
    Tuple model.toRVSDG.Val (Threaded carried) :=
  withRuntime token (.cons payload (.cons ⟨1⟩ .nil))

private theorem body_keeps_going (fuel payload token : Nat) :
    body.1.run model.toRVSDG fuel (carriedInput payload token) =
      some (.cons ⟨1⟩ (carriedInput (payload + 1) (2 * token + (payload + 1)))) := rfl

private def keepsGoing (tag : model.toRVSDG.Val (.control 2)) : Bool := tag.down.val == 1

private theorem iterate_no_return (bodyFuel fuel payload token : Nat) :
    iterate (body.1.run model.toRVSDG bodyFuel) keepsGoing
      fuel (carriedInput payload token) = none := by
  induction fuel generalizing payload token with
  | zero => rfl
  | succ fuel ih =>
    change (match body.1.run model.toRVSDG bodyFuel (carriedInput payload token) with
      | none => none
      | some (.cons tag next) =>
        if keepsGoing tag then iterate (body.1.run model.toRVSDG bodyFuel) keepsGoing fuel next
        else some next) = none
    rw [body_keeps_going]
    exact ih _ _

private theorem selected_loop_no_return (fuel : Nat) :
    graph.run model.toRVSDG fuel (input 1 1 7 9 0) = none := by
  refine (graph.run_toTerm model.toRVSDG fuel (input 1 1 7 9 0)).symm.trans ?_
  change program.1.toGraph.toTerm.run model.toRVSDG fuel (input 1 1 7 9 0) = none
  rw [Term.toTerm_toGraph]
  change (Option.bind (Option.bind
    (iterate (body.1.run model.toRVSDG fuel) keepsGoing fuel (carriedInput 2 0)) _) _) = none
  rw [iterate_no_return]
  rfl

-- Even at empty data demand, selecting the diverging arm gives no finite return.
example : ¬ ∃ out, graph.Returns model.toRVSDG (input 1 1 70 90 0) out := by
  rw [← graph.hasFiniteReturn_iff_of_demand model.toRVSDG stateOnly _ _
    (captures_agree stateOnly (by decide) (by decide) 1)]
  rintro ⟨out, fuel, returned⟩
  rw [selected_loop_no_return] at returned
  contradiction

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Regression
