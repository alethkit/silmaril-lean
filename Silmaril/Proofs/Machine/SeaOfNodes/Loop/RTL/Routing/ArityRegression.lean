module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Result)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model)

private def mem : Memory := Memory.ofList 4 [39, 17, 83, 10]

private def checkedRun (payloads : Nat) (entry feedback : List Nat) (result fuel : Nat)
    (input : List Word) : Option (Result Reg) :=
  (lowerBankChecked payloads entry feedback result).map (fun prog => prog.runMain fuel 0 input mem)

-- The sole payload reads the old counter while the new counter decrements.
example : checkedRun 1 [1] [2] 0 17 [2, 99] = some (.returned [1] mem) := by cbv

private def wide : BankRoutes 5 :=
  ⟨.cons (.arg (argumentPort 6 5))
      (.cons (.arg (argumentPort 6 1)) (.cons (.arg (argumentPort 6 2))
        (.cons (.arg (argumentPort 6 3)) (.cons (.arg (argumentPort 6 4)) .nil)))),
    .cons (.arg (argumentPort 12 8))
      (.cons (.arg (argumentPort 12 7)) (.cons (.arg (argumentPort 12 11))
        (.cons (.arg (argumentPort 12 7)) (.cons (.arg (argumentPort 12 9)) .nil)))),
    3⟩

private theorem accepted :
    lowerBankChecked 5 [5, 1, 2, 3, 4] [8, 7, 11, 7, 9] 3 = some wide.lower := by cbv

example : checkBankRoutes 5 [5, 1, 2, 3, 4] [8, 7, 11, 7, 9] 3 = some wide := by cbv
example : wide.lower.WellFormed := bank_checked_wellFormed accepted

private def input : WordTuple 6 :=
  .cons (1 : Word) (.cons (10 : Word) (.cons (20 : Word) (.cons (30 : Word)
    (.cons (40 : Word) (.cons (50 : Word) .nil)))))

private def latched : WordTuple 6 :=
  .cons (0 : Word) (.cons (10 : Word) (.cons (50 : Word) (.cons (40 : Word)
    (.cons (50 : Word) (.cons (20 : Word) .nil)))))

-- Both repeated reads of register 7 retain 50 after register 7 receives 10.
private def feedbackSnapshot : Option (List Word) :=
  match wide.lower.runMain 6 0 (words input) mem with
  | .running s =>
    if s.point.label = 1 ∧ s.point.index = 0 then s.frame.readAll (paramRegs 6 6) else none
  | _ => none

example : feedbackSnapshot = some [0, 10, 50, 40, 50, 20] := by cbv

-- Return slot 3 observes the second read of old register 7.
example : checkedRun 5 [5, 1, 2, 3, 4] [8, 7, 11, 7, 9] 3 12 (words input) =
    some (.returned [50] mem) := by cbv

private theorem native_return :
    wide.graph.ReturnsAfter model input 1 (wide.graph.initial model input) (50 : Word) :=
  .backedge (next := latched) (by cbv) (.exit (by cbv))

example : wide.lower.oracle 0 (words input) mem [50] mem :=
  (bank_returns_iff wide input mem mem [50]).mpr ⟨50, ⟨1, native_return⟩, rfl, rfl⟩

example : lowerBankChecked 5 [5, 1, 2, 3, 4] [8, 7, 11, 7, 9] 5 = none := by cbv
example : lowerBankChecked 0 [] [] 0 = none := lowerBankChecked_zero [] [] 0

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
