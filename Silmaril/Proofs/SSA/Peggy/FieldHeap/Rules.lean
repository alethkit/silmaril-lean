module

public import Silmaril.SSA.Peggy.FieldHeap.Defs

public section

namespace Silmaril.SSA.Peggy.FieldHeap.Proofs

open Silmaril.Semantics.Operational (Environment)

variable {state : State} {receiver : Receiver} {field : Field}

theorem locate_ok_iff {id : ObjectId} {fields : Object} {old : Int} :
    state.locate receiver field = .ok ⟨id, fields, old⟩ ↔
      receiver = .object id ∧ state.fault = none ∧ state.heap id = some fields ∧
        fields field = some old := by
  constructor
  · intro found
    cases fault : state.fault with
    | some e => simp [State.locate, fault] at found
    | none =>
      cases receiver with
      | null => simp [State.locate, Heap.locate, fault] at found
      | object address =>
        cases allocated : state.heap address with
        | none => simp [State.locate, Heap.locate, fault, allocated] at found
        | some actualFields =>
          cases present : actualFields field with
          | none => simp [State.locate, Heap.locate, fault, allocated, present] at found
          | some value =>
            simp [State.locate, Heap.locate, fault, allocated, present] at found
            rcases found with ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, allocated, present⟩
  · rintro ⟨rfl, live, allocated, present⟩
    simp [State.locate, Heap.locate, live, allocated, present]

theorem getField_setField (state : State) (receiver : Receiver) (field : Field) (value : Int) :
    getField (setField state receiver field value) receiver field =
      forwardRead (setField state receiver field value) value := by
  cases found : state.locate receiver field with
  | error fault =>
    simp only [setField, found]
    rfl
  | ok cell =>
    rcases cell with ⟨id, fields, old⟩
    obtain ⟨rfl, live, _, _⟩ := locate_ok_iff.mp found
    simp only [setField, found]
    simp [getField, State.locate, Heap.locate, ReadResult.ofAccess, Except.map, forwardRead, live]

private theorem getField_setField_value (allowed : Accessible state receiver field) (value : Int) :
    (getField (setField state receiver field value) receiver field).value = some value := by
  rcases allowed with ⟨id, fields, old, rfl, live, allocated, present⟩
  have found : state.locate (.object id) field = .ok ⟨id, fields, old⟩ :=
    locate_ok_iff.mpr ⟨rfl, live, allocated, present⟩
  rw [getField_setField]
  simp [setField, found, forwardRead, live]

theorem getField_setField_value_iff (state : State) (receiver : Receiver) (field : Field) (value : Int) :
    (getField (setField state receiver field value) receiver field).value = some value ↔
      Accessible state receiver field := by
  refine ⟨?_, fun allowed => getField_setField_value allowed value⟩
  intro loaded
  cases found : state.locate receiver field with
  | error fault =>
    rw [getField_setField] at loaded
    simp [setField, forwardRead, found] at loaded
  | ok cell =>
    rcases cell with ⟨id, fields, old⟩
    exact ⟨id, fields, old, locate_ok_iff.mp found⟩

private theorem locate_value_set_other (heap : Heap) {id : ObjectId} {fields : Object}
    (allocated : heap id = some fields) {written read : Field} (value : Int) {receiver : Receiver}
    (disjoint : Disjoint receiver read (.object id) written) :
    (Heap.locate (Environment.set heap id (Environment.set fields written value)) receiver read).map
        Cell.value =
      (Heap.locate heap receiver read).map Cell.value := by
  cases receiver with
  | null => rfl
  | object address =>
    by_cases same : address = id
    · subst address
      have different : read ≠ written := disjoint.resolve_left (fun h => h rfl)
      simp only [Heap.locate, Environment.set_same, allocated,
        Environment.set_other fields written read value different]
      cases fields read <;> rfl
    · simp [Heap.locate, Environment.set_other heap id address _ same]

theorem getField_setField_disjoint (allowed : Accessible state receiver field) (value : Int)
    {other : Receiver} {read : Field} (disjoint : Disjoint other read receiver field) :
    getField (setField state receiver field value) other read =
      { getField state other read with
        state := { (getField state other read).state with heap := (setField state receiver field value).heap } } := by
  rcases allowed with ⟨id, fields, old, rfl, live, allocated, present⟩
  have found : state.locate (.object id) field = .ok ⟨id, fields, old⟩ :=
    locate_ok_iff.mpr ⟨rfl, live, allocated, present⟩
  let writtenHeap := Environment.set state.heap id (Environment.set fields field value)
  have frame : (Heap.locate writtenHeap other read).map Cell.value =
      (Heap.locate state.heap other read).map Cell.value :=
    locate_value_set_other state.heap allocated value disjoint
  simp only [setField, found]
  simp only [getField, State.locate, live]
  change ReadResult.ofAccess { heap := writtenHeap, fault := none }
    ((Heap.locate writtenHeap other read).map Cell.value) = _
  rw [frame]
  cases (Heap.locate state.heap other read).map Cell.value with
  | error fault => rfl
  | ok result => simp [ReadResult.ofAccess, live, writtenHeap]

theorem setField_setField (state : State) (receiver : Receiver) (field : Field) (first last : Int) :
    setField (setField state receiver field first) receiver field last =
      setField state receiver field last := by
  cases found : state.locate receiver field with
  | error fault =>
    simp only [setField, found]
    rfl
  | ok cell =>
    rcases cell with ⟨id, fields, old⟩
    obtain ⟨rfl, live, _, _⟩ := locate_ok_iff.mp found
    simp only [setField, found]
    simp [State.locate, Heap.locate, live, Environment.set_set]

theorem ordered_injective : Function.Injective ReadResult.ordered := by
  intro a b same
  have state : a.state = b.state :=
    Option.some.inj (congrArg (fun ports : Observation => ports.get .head) same)
  have value : a.value = b.value :=
    Option.some.inj (congrArg (fun ports : Observation => ports.get (.tail .head)) same)
  cases a
  cases b
  cases state
  cases value
  rfl

end Silmaril.SSA.Peggy.FieldHeap.Proofs
