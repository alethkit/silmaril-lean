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
    .cons (.arg (argumentPort 8 6))
      (.cons (.arg (argumentPort 8 5)) (.cons (.arg (argumentPort 8 6)) .nil)),
    1⟩

private def spec : FeedbackSpec := ⟨.sub, 1, 0, 2⟩
private def update : FeedbackUpdate 3 := ⟨.sub, 1, 0, 2⟩
private def input : WordTuple 4 := pack 1 10 20 30

private theorem admitted :
    lowerComputedChecked 3 [1, 2, 3] [6, 5, 6] 1 spec = some (routes.lowerWith (some update)) := by
  cbv

example : spec.check 3 = some update := by cbv
example : (routes.lowerWith (some update)).WellFormed := computed_checked_wellFormed admitted

-- The first copy overwrites the left input of subtraction. The last
-- copy also reads the old destination of the subtraction.
example : routes.incomingWith (some update) .backedge = [.node 1, .arg 6, .node 4, .arg 6] := rfl

private def feedbackSnapshot : Option (List Word) :=
  match (routes.lowerWith (some update)).runMain 7 0 (words input) mem with
  | .running state =>
    if state.point.label = 1 ∧ state.point.index = 0 then state.frame.readAll (paramRegs 4 4) else none
  | _ => none

example : feedbackSnapshot = some [0, 20, -20, 20] := by cbv

example : (routes.lowerWith (some update)).runMain 14 0 (words input) mem = .returned [-20] mem := by cbv

example : (routes.lowerWith (some update)).runMain 8 0 [0, 10, 20, 30] mem = .returned [20] mem := by cbv

example :
    (lowerComputedChecked 3 [1, 2, 3] [6, 5, 6] 1 ⟨.add, 1, 0, 2⟩).map
      (fun prog => prog.runMain 14 0 [1, -1, 20, 2] mem) = some (.returned [1] mem : Result Reg) := by cbv

private theorem nativeReturn :
    (routes.graphWith (some update)).ReturnsAfter model input 1
      ((routes.graphWith (some update)).initial model input) (-20 : Word) :=
  .backedge (next := pack 0 20 (-20) 20) (by cbv) (.exit (by cbv))

example : (routes.lowerWith (some update)).oracle 0 (words input) mem [-20] mem :=
  (computed_returns_iff routes update input mem mem [-20]).mpr ⟨-20, ⟨1, nativeReturn⟩, rfl, rfl⟩

-- Arithmetic can read payload slots 0 through 2. An index outside that
-- bank, or a destination outside the bank, fails the checked lowering.
example : lowerComputedChecked 3 [1, 2, 3] [6, 5, 6] 1 ⟨.sub, 1, 3, 2⟩ = none := by cbv
example : lowerComputedChecked 3 [1, 2, 3] [6, 5, 6] 1 ⟨.sub, 3, 0, 2⟩ = none := by cbv

example : lowerComputedChecked 3 [1, 2, 3] [6, 6] 1 spec = none := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
