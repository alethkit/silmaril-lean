module

import Silmaril.SSA.PEG.Builder
import Silmaril.SSA.Peggy.FieldHeap.Linearize.Thms

namespace Silmaril.SSA.Peggy.FieldHeap.Linearize.Tests

open RVSDG (Tuple)
open Silmaril.Semantics.Operational (Environment)

private abbrev Params : List (PEG.Ty DataSort) := [stateTy, receiverTy, receiverTy, intTy]

private def sorts : Fin 11 → PEG.Ty DataSort :=
  Fin.cases stateTy (Fin.cases receiverTy (Fin.cases receiverTy (Fin.cases intTy
    (Fin.cases readTy (Fin.cases stateTy (Fin.cases stateTy (Fin.cases readTy
      (Fin.cases stateTy (Fin.cases readValueTy (Fin.cases readValueTy Fin.elim0))))))))))

/-- The first read is still observed in the forked variant. Only its successor
store changes: it consumes the entry token instead of the first read's token. -/
private def raw (forked : Bool) : PEG.RawGraph Op Params (stateTy :: ReadTypes 3) 11 0 where
  forest := ⟨Fin.elim0⟩
  sort := sorts
  node := Fin.cases (motive := fun i => PEG.RawNode Op Params 0 (sorts i))
    ⟨[], .param .head, []⟩
    (Fin.cases ⟨[], .param (.tail .head), []⟩
    (Fin.cases ⟨[], .param (.tail (.tail .head)), []⟩
    (Fin.cases ⟨[], .param (.tail (.tail (.tail .head))), []⟩
    (Fin.cases ⟨_, .op (.getField 3), [0, 1]⟩
    (Fin.cases ⟨_, .op .readState, [4]⟩
    (Fin.cases ⟨_, .op (.setField 3), [if forked then 0 else 5, 2, 3]⟩
    (Fin.cases ⟨_, .op (.getField 3), [6, 2]⟩
    (Fin.cases ⟨_, .op .readState, [7]⟩
    (Fin.cases ⟨_, .op .readValue, [4]⟩
    (Fin.cases ⟨_, .op .readValue, [7]⟩ (fun i => i.elim0)))))))))))
  roots := [8, 10, 9, 10]

private def graph (forked : Bool) : Graph Params 3 11 :=
  (raw forked).check.get (by cases forked <;> decide)

private def schedule : Schedule Params 11 :=
  .load
    (.store (.load (.entry .head) 4 3 (.tail .head)) 6 3
      (.tail (.tail .head)) (.tail (.tail (.tail .head))))
    7 3 (.tail (.tail .head))

private def program : Program Params 3 11 :=
  ⟨schedule, .cons 7 (.cons 4 (.cons 7 .nil))⟩

private theorem accepted : linearize (graph false) = .ok program := rfl

private theorem forkRejected : linearize (graph true) = .error .unsequencedEffect := rfl

-- Sharing a load result is fine. Sharing the token between potentially
-- conflicting accesses requires a different ordering argument.
example : program.schedule.effects.reverse = [4, 6, 7] := rfl
example : PEG.DemandRank.check [.phase Fin.val] (graph true) = true := rfl
example : linearize (graph false) (fun _ => 0) = .error .demandOrder := rfl

private def entry : State :=
  State.initial (Environment.set Environment.empty 10 (Environment.set Environment.empty 3 (-3)))

private def target : Receiver := .object 10

private def input (before store : Receiver) : Inputs Params :=
  .cons entry (.cons before (.cons store (.cons (99 : Int) .nil)))

private def expected (state : State) (last first : Option Int) : Outputs 3 :=
  .cons (some state) (.cons (some last) (.cons (some first) (.cons (some last) .nil)))

private theorem aliased :
    program.run (input target target) =
      expected (setField entry target 3 99) (some 99) (some (-3)) := rfl

private theorem firstFault :
    program.run (input .null (.object 77)) =
      expected { entry with fault := some .nullReceiver } none none := rfl

private theorem earlierReadSurvives :
    program.run (input target .null) =
      expected { entry with fault := some .nullReceiver } none (some (-3)) := rfl

-- Link the executable result to the actual guarded Figure 11 observation.
example :
    (graph false).observe interpretation
        ((graph false).denote interpretation (input target target) (demandWellFounded accepted)) Fin.elim0 =
      expected (setField entry target 3 99) (some 99) (some (-3)) :=
  (run_eq_observe accepted (input target target) Fin.elim0).symm.trans aliased

example :
    (graph false).observe interpretation
        ((graph false).denote interpretation (input .null (.object 77)) (demandWellFounded accepted)) Fin.elim0 =
      expected { entry with fault := some .nullReceiver } none none :=
  (run_eq_observe accepted (input .null (.object 77)) Fin.elim0).symm.trans firstFault

-- A load with its original token sees the old value even through aliased
-- receiver parameters. Moving it after the write would change that value.
example : (getField entry target 3).value ≠ (getField (setField entry target 3 99) target 3).value :=
  by decide

-- The fork can combine a null read of the entry snapshot with a successful
-- store on that separate snapshot. Either serial order would latch the fault.
example :
    (getField entry .null 3).value = none ∧
    (setField entry target 3 99).fault = none ∧
    (setField (getField entry .null 3).state target 3 99).fault = some .nullReceiver ∧
    (getField (setField entry target 3 99) .null 3).state.fault = some .nullReceiver :=
  ⟨rfl, rfl, rfl, rfl⟩

end Silmaril.SSA.Peggy.FieldHeap.Linearize.Tests
