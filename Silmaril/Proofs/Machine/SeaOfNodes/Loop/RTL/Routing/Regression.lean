module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Result)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model)

private def rotated : Routes :=
  ⟨.cons (.arg (argumentPort 4 3))
    (.cons (.arg (argumentPort 4 1)) (.cons (.arg (argumentPort 4 2)) .nil)),
   .cons (.arg (argumentPort 8 6))
    (.cons (.arg (argumentPort 8 7)) (.cons (.arg (argumentPort 8 5)) .nil))⟩

private theorem accepted : lowerChecked [3, 1, 2] [6, 7, 5] = some rotated.lower := by cbv

example : checkRoutes [3, 1, 2] [6, 7, 5] = some rotated := by cbv
example : rotated.lower.WellFormed := checked_wellFormed accepted

private def mem : Memory := Memory.ofList 4 [19, 29, 71, 83]

example : rotated.incomingRegisters .entry = [.arg 0, .arg 3, .arg 1, .arg 2] := rfl
example : rotated.incomingRegisters .backedge = [.node 1, .arg 6, .arg 7, .arg 5] := rfl

-- Entry routing gives (30, 10, 20). The feedback rotation must read all
-- three old values, including the first slot that has already been written
-- in a sequential left-to-right copy.
private def afterFeedback : Option (List Word) :=
  match rotated.lower.runMain 6 0 [1, 10, 20, 30] mem with
  | .running s =>
    if s.point.label = 1 ∧ s.point.index = 0 then s.frame.readAll bankParams else none
  | _ => none

example : afterFeedback = some [0, 10, 20, 30] := by cbv

example : rotated.lower.runMain 7 0 [0, 10, 20, 30] mem = .returned [30] mem := by cbv
example : rotated.lower.runMain 12 0 [1, 10, 20, 30] mem = .returned [10] mem := by cbv
example : rotated.lower.runMain 17 0 [2, 10, 20, 30] mem = .returned [20] mem := by cbv

private def input := pack 1 10 20 30

private theorem native_return :
    rotated.graph.ReturnsAfter model input 1 (rotated.graph.initial model input) (10 : Word) :=
  .backedge (next := pack 0 10 20 30) (by cbv) (.exit (by cbv))

example : rotated.lower.oracle 0 [1, 10, 20, 30] mem [10] mem :=
  (lower_returns_iff rotated input mem mem [10]).mpr ⟨10, ⟨1, native_return⟩, rfl, rfl⟩

-- A repeated operand is an admitted route. The first result is the old
-- third payload, while the second and third now both read the old first.
example :
    (lowerChecked [3, 1, 2] [7, 5, 5]).map (fun p => p.runMain 12 0 [1, 10, 20, 30] mem) =
      some (.returned [20] mem : Result Reg) := by cbv

example : lowerChecked [3, 1, 2] [6, 8, 5] = none := by cbv
example : lowerChecked [3, 1] [6, 7, 5] = none := by cbv

-- The standalone column API also handles arities outside the loop profile.
example : (checkColumn 4 5 [1, 1, 2, 0, 3]).map emitColumn =
    some [Reg.arg 1, .arg 1, .arg 2, .arg 0, .arg 3] := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
