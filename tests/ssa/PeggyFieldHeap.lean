module

import Silmaril.SSA.Peggy.FieldHeap.Thms
import Silmaril.SSA.PEG.Semantics.Thms

namespace Silmaril.SSA.Peggy.FieldHeap.Tests

open Silmaril.Semantics.Operational (Environment)
open RVSDG (Tuple)

private def objectFields : Object :=
  Environment.set (Environment.set Environment.empty 3 (-3)) 4 17

private def otherFields : Object := Environment.set Environment.empty 3 41

private def heap : Heap :=
  Environment.set (Environment.set Environment.empty 10 objectFields) 11 otherFields

private def entry : State := State.initial heap
private def target : Receiver := .object 10
private def aliasedReceiver : Receiver := .object 10
private def other : Receiver := .object 11

private theorem accessible : Accessible entry target 3 :=
  ⟨10, objectFields, -3, rfl, rfl, rfl, rfl⟩

-- The receiver slot identity is irrelevant when both values name the same object.
example : (getField (setField entry target 3 99) aliasedReceiver 3).value = some 99 := by decide
example : (getField (setField entry target 3 99) aliasedReceiver 3).value ≠ (getField entry aliasedReceiver 3).value :=
  by decide

example : (getField (setField entry target 3 99) aliasedReceiver 4).value = some 17 := by decide
example : (getField (setField entry target 3 99) other 3).value = some 41 := by decide

example : getField (setField entry target 3 99) .null 4 =
    ⟨{ setField entry target 3 99 with fault := some .nullReceiver }, none⟩ :=
  getField_setField_disjoint accessible 99 (.inl (by decide))

example : (getField (setField (setField entry target 3 5) target 3 6) aliasedReceiver 3).value = some 6 :=
  by decide

example : (getField entry (.object 99) 3).state.fault = some (.unallocated 99) := by decide
example : setField entry (.object 99) 3 7 = { entry with fault := some (.unallocated 99) } := rfl
example : (setField entry target 5 99).fault = some (.absentField 10 5) := by decide
example : (setField (setField entry .null 3 99) (.object 99) 3 7).fault = some .nullReceiver :=
  by decide

-- A disjoint receiver is insufficient when the write itself fails.
example : Disjoint aliasedReceiver 4 .null 3 := .inl (by decide)
example : (getField (setField entry .null 3 99) aliasedReceiver 4).value ≠ (getField entry aliasedReceiver 4).value :=
  by decide

-- A faulting read preserves an already completed store.
example : ((getField (setField entry target 3 99) .null 4).state.heap 10 >>= (· 3)) = some 99 :=
  by decide

private abbrev inputs : List (PEG.Ty DataSort) := [stateTy, receiverTy, intTy]

universe u

-- Both the typed node table and the proposed valuation use the same row indices.
private def caseRow {F : Fin 7 → Sort u} (a : F 0) (b : F 1) (c : F 2) (d : F 3)
    (e : F 4) (f : F 5) (g : F 6) (i : Fin 7) : F i :=
  Fin.cases a (fun i =>
    Fin.cases b (fun i =>
      Fin.cases c (fun i =>
        Fin.cases d (fun i =>
          Fin.cases e (fun i =>
            Fin.cases f (fun i => Fin.cases g (fun empty => empty.elim0) i) i) i) i) i) i) i

private def sorts (i : Fin 7) : PEG.Ty DataSort :=
  caseRow (F := fun _ => PEG.Ty DataSort) stateTy receiverTy intTy stateTy readTy stateTy readValueTy i

private def initialRef : PEG.Ref sorts stateTy := ⟨0, rfl⟩
private def receiverRef : PEG.Ref sorts receiverTy := ⟨1, rfl⟩
private def intRef : PEG.Ref sorts intTy := ⟨2, rfl⟩
private def writtenRef : PEG.Ref sorts stateTy := ⟨3, rfl⟩
private def readRef : PEG.Ref sorts readTy := ⟨4, rfl⟩

/-- Both candidates consume the store's token. The second replaces the load with forwarding. -/
private def graph (forward : Bool) : PEG.Graph Op inputs observationTypes 7 0 where
  forest := ⟨Fin.elim0⟩
  sort := sorts
  node i := caseRow (F := fun row => PEG.Node Op inputs (Fin 0) sorts (sorts row))
    (.ofLabel (.param .head) .nil)
    (.ofLabel (.param (.tail .head)) .nil)
    (.ofLabel (.param (.tail (.tail .head))) .nil)
    (.ofLabel (.op (.setField 3)) (.cons initialRef (.cons receiverRef (.cons intRef .nil))))
    (if forward then .ofLabel (.op .forwardRead) (.cons writtenRef (.cons intRef .nil))
      else .ofLabel (.op (.getField 3)) (.cons writtenRef (.cons receiverRef .nil)))
    (.ofLabel (.op .readState) (.cons readRef .nil))
    (.ofLabel (.op .readValue) (.cons readRef .nil)) i
  roots := .cons ⟨5, rfl⟩ (.cons ⟨6, rfl⟩ .nil)

private theorem wf (forward : Bool) : WellFounded (graph forward).Demand :=
  (graph forward).demandWellFounded_of_check [.phase Fin.val] (by cases forward <;> decide)

private def env (s : State) (r : Receiver) (v : Int) : Tuple interpretation.Value inputs :=
  .cons s (.cons r (.cons v .nil))

private def result (forward : Bool) (s : State) (r : Receiver) (v : Int) : ReadResult :=
  let written := setField s r 3 v
  if forward then forwardRead written v else getField written r 3

private def values (forward : Bool) (s : State) (r : Receiver) (v : Int) :
    (graph forward).Valuation interpretation := fun (i, _) =>
  caseRow (F := fun row => Option (interpretation.Value (sorts row)))
    (some s) (some r) (some v) (some (setField s r 3 v)) (some (result forward s r v))
    (some (result forward s r v).state) (some (result forward s r v).value) i

private theorem solves (forward : Bool) (s : State) (r : Receiver) (v : Int) :
    (graph forward).Solves interpretation (env s r v) (values forward s r v) := by
  rintro ⟨i, index⟩
  refine caseRow (F := fun row => values forward s r v (row, index) =
    (graph forward).equation interpretation (env s r v) (values forward s r v) (row, index))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ i
  all_goals cases forward <;> rfl

private noncomputable def program (forward : Bool) (s : State) (r : Receiver) (v : Int) : Observation :=
  observe (graph forward) (env s r v) (wf forward) Fin.elim0

private theorem program_eq (forward : Bool) (s : State) (r : Receiver) (v : Int) :
    program forward s r v = (result forward s r v).ordered := by
  unfold program observe
  rw [(graph forward).solves_unique interpretation (env s r v) (wf forward)
      ((graph forward).denote_solves interpretation (env s r v) (wf forward)) (solves forward s r v)]
  rfl

-- The whole Figure 11 observation, including the final heap and fault, is equal.
example (s : State) (r : Receiver) (v : Int) : program false s r v = program true s r v :=
  (program_eq false s r v).trans ((congrArg ReadResult.ordered (getField_setField s r 3 v)).trans
    (program_eq true s r v).symm)

example : program false entry target 99 =
    (ReadResult.mk (setField entry target 3 99) (some 99)).ordered := by
  rw [program_eq]
  rfl

example : program true entry .null 99 =
    (ReadResult.mk { entry with fault := some .nullReceiver } none).ordered := by
  rw [program_eq]
  rfl

example : (program false entry (.object 99) 99).get (.tail .head) = some none := by
  rw [program_eq]
  rfl

-- Returning the proposed value after a fault would change the observed read port.
example : (program false entry .null 99).get (.tail .head) ≠ some (some (99 : Int)) := by
  intro equal
  rw [program_eq] at equal
  change some (none : Option Int) = some (some (99 : Int)) at equal
  cases Option.some.inj equal

end Silmaril.SSA.Peggy.FieldHeap.Tests
