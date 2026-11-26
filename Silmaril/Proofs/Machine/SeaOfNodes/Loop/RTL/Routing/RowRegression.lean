module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Result)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model)

private def mem : Memory := Memory.ofList 4 [49, 27, 13, 54]

private def routes : BankRoutes 3 :=
  ⟨.cons (.arg (argumentPort 4 1))
      (.cons (.arg (argumentPort 4 2)) (.cons (.arg (argumentPort 4 3)) .nil)),
    .cons (.arg (argumentPort 8 5))
      (.cons (.arg (argumentPort 8 6)) (.cons (.arg (argumentPort 8 5)) .nil)),
    1⟩

private def specs : List FeedbackSpec := [⟨.sub, 0, 1, 2⟩, ⟨.add, 1, 0, 1⟩]
private def updates : List (FeedbackUpdate 3) := [⟨.sub, 0, 1, 2⟩, ⟨.add, 1, 0, 1⟩]
private def input : WordTuple 4 := pack 1 10 20 30

private theorem checked :
    lowerFeedbackRowChecked 3 [1, 2, 3] [5, 6, 5] 1 specs = some (routes.lowerWithRow updates) := by
  cbv

example : checkFeedbackRow 3 specs = some updates := by cbv
example : (routes.lowerWithRow updates).WellFormed := row_checked_wellFormed checked

-- Each arithmetic update uses the other's old destination. The last slot copies old slot zero.
example : routes.incomingWithRow updates .backedge = [.node 1, .node 4, .node 5, .arg 5] := rfl
example : routes.incomingWithRow updates.reverse .backedge = [.node 1, .node 5, .node 4, .arg 5] := rfl

private def feedbackSnapshot : Option (List Word) :=
  match (routes.lowerWithRow updates).runMain 8 0 (words input) mem with
  | .running state =>
    if state.point.label = 1 ∧ state.point.index = 0 then state.frame.readAll (paramRegs 4 4) else none
  | _ => none

example : feedbackSnapshot = some [0, -10, 30, 10] := by cbv
example : (routes.lowerWithRow updates).runMain 16 0 (words input) mem = .returned [30] mem := by cbv

example :
    (lowerFeedbackRowChecked 3 [1, 2, 3] [5, 6, 5] 1 specs.reverse).map
      (fun prog => prog.runMain 16 0 (words input) mem) = some (.returned [30] mem : Result Reg) := by cbv

example : (routes.lowerWithRow updates).runMain 9 0 [0, 10, 20, 30] mem = .returned [20] mem := by cbv

private theorem nativeReturn :
    (routes.graphWithRow updates).ReturnsAfter model input 1
      ((routes.graphWithRow updates).initial model input) (30 : Word) :=
  .backedge (next := pack 0 (-10) 30 10) (by cbv) (.exit (by cbv))

example : (routes.lowerWithRow updates).oracle 0 (words input) mem [30] mem :=
  (row_returns_iff routes updates input mem mem [30]).mpr ⟨30, ⟨1, nativeReturn⟩, rfl, rfl⟩

example : lowerFeedbackRowChecked 3 [1, 2, 3] [5, 6, 5] 1
    [⟨.sub, 0, 1, 2⟩, ⟨.add, 0, 0, 1⟩] = none := by cbv

example : lowerFeedbackRowChecked 3 [1, 2, 3] [5, 6, 5] 1
    [⟨.sub, 0, 1, 2⟩, ⟨.add, 3, 0, 1⟩] = none := by cbv

example : lowerFeedbackRowChecked 3 [1, 2, 3] [5, 6, 5] 1 [] = some routes.lower := by cbv

example : lowerFeedbackRowChecked 3 [1, 2, 3] [5, 6, 5] 1 [⟨.sub, 0, 1, 2⟩] =
    lowerComputedChecked 3 [1, 2, 3] [5, 6, 5] 1 ⟨.sub, 0, 1, 2⟩ :=
  lowerFeedbackRowChecked_singleton 3 [1, 2, 3] [5, 6, 5] 1 ⟨.sub, 0, 1, 2⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
