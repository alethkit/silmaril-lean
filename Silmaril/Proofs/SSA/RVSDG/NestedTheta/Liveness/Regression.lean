module

import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Regression

open OrderedRuntime
open Structured (Data Opcode RuntimeValues Threaded nextRuntime runtimePort withRuntime)
open ExplicitRuntime (EntryChecked)

private abbrev Ty := Structured.Ty Unit
private abbrev val : Ty := .value ()
private abbrev value : Ports Ty := [val]
private abbrev armArgs : Ports Ty := [val, val]
private abbrev entry : Ports Ty := .control 2 :: val :: val :: val :: []
private abbrev stepOut : Ports Ty := Theta.BodyResults value
private abbrev valueData : Data value := .value .nil
private abbrev armData : Data armArgs := .value valueData
private abbrev entryData : Data entry := .control (.value armData)
private abbrev stepData : Data stepOut := .control valueData

private abbrev Pure : Dialect Unit PUnit := fun _ _ => Empty
private inductive Effect : Dialect Unit PUnit where
  | charge : Effect value value
  | advance : Effect value stepOut

private abbrev Op := Opcode Pure Effect

private def model : Structured.Model Pure Effect (StateM Nat) where
  value _ := Nat
  runPure op _ := nomatch op
  effect
    | .charge, input => fun token => (input, token + 10)
    | .advance, .cons payload .nil => fun token =>
      let next := (show Nat from payload) + 1
      let tag : Fin 2 := if next < 4 then 1 else 0
      (.cons ⟨tag⟩ (.cons next .nil), 2 * token + next)

private abbrev CheckedTerm {ins outs : Ports Ty} (i : Data ins) (o : Data outs)
    (sigs : List (Ports Ty)) :=
  Σ t : Term Op (Threaded ins) [] sigs (Threaded outs), EntryChecked (a := i) (b := o) t

private def arms (tag : Fin 2) :
    CheckedTerm armData valueData (Fin.cases [] (fun _ => [Threaded value]) tag) :=
  Fin.cases
    ⟨_, .ret (.arg (runtimePort armArgs)) (.cons (.arg .head) .nil)⟩
    (fun _ => ⟨_, .primitive (.arg (runtimePort armArgs)) valueData valueData (.effect .charge)
      (.cons (.arg .head) .nil)
      (.ret (nextRuntime [] value) (.cons (.output (0 : Fin 1) .head) .nil))⟩) tag

private def body : CheckedTerm valueData stepData [Threaded stepOut] :=
  ⟨_, .primitive (.arg (runtimePort value)) valueData stepData (.effect .advance)
    (.cons (.arg .head) .nil)
    (.ret (nextRuntime [] stepOut)
      (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

private def program : CheckedTerm entryData valueData [Threaded value, Threaded value] :=
  ⟨_, .gamma 0 (.arg .head) (.arg (runtimePort entry)) armData valueData
    (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
    (Fin.cases [] (fun _ => [Threaded value]))
    (children := fun tag => (arms tag).1) (fun tag => (arms tag).2)
    (.theta (nextRuntime [] value) valueData (.cons (.arg (.tail .head)) .nil)
      [Threaded stepOut] (children := fun _ => body.1) (fun _ => body.2)
      (.ret (nextRuntime [Threaded value] value) (.cons (.output (1 : Fin 2) .head) .nil)))⟩

private def graph := program.1.toGraph

private def input (tag : Fin 2) (unused token : Nat) :
    Tuple (RuntimeValues model.value Nat) (Threaded entry) :=
  withRuntime token (.cons ⟨tag⟩ (.cons (2 : Nat) (.cons (99 : Nat) (.cons unused .nil))))

private def result (payload token : Nat) : Tuple (RuntimeValues model.value Nat) (Threaded value) :=
  withRuntime token (.cons payload .nil)

-- Both vertices kill their own outputs. θ uses γ's token but ignores its data result.
example : graph.liveAt 0 = [.arg 0, .arg 1, .arg 2, .arg 4] := by decide
example : graph.liveAt 1 = [.arg 1, .output 0 1] := by decide
example : graph.liveAt 2 = [.output 1 0, .output 1 1] := by decide
example : graph.liveAt 3 = [] := by decide

-- Child liveness stays local. Although both arms ignore their second argument,
-- the parent's may solution retains the corresponding γ operand.
example : Address.arg 2 ∈ graph.liveness.mayOut 0 :=
  (graph.mem_liveAt_iff 0 _).1 (by decide)
example : Address.arg 1 ∉ (arms 0).1.toGraph.liveAt 0 := by decide
example : Address.arg 1 ∉ (arms 1).1.toGraph.liveAt 0 := by decide

private theorem agrees (tag : Fin 2) (token unused : Nat) :
    graph.AgreesOnLiveInputs (input tag 0 token) (input tag unused token) := by
  intro ty p live
  have listed := (graph.mem_liveAt_iff 0 _).2 live
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
        | head => exact False.elim ((by decide : Address.arg 3 ∉ graph.liveAt 0) listed)
        | tail p =>
          cases p with
          | head => rfl
          | tail p => nomatch p

-- The selected arm charges the state before two iterations of the θ body.
-- Transport the exact observation across a change to the unwired entry slot.
example : ExplicitRuntime.observe model graph program.2.collect (input 1 200 0) =
    Part.some (ExplicitRuntime.boundaryResult (result 4 50)) :=
  (ExplicitRuntime.observe_eq_some model graph program.2.collect _ _).2
    ((graph.returns_congr_of_live model.toRVSDG _ _ (agrees 1 0 200) _).1 ⟨2, rfl⟩)

-- The selector and initial token are live: changing either changes the observation.
example : graph.run model.toRVSDG 2 (input 0 0 0) = some (result 4 10) := rfl
example : graph.run model.toRVSDG 2 (input 0 0 1) = some (result 4 14) := rfl
example : graph.run model.toRVSDG 1 (input 1 0 0) = none := rfl

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Regression
