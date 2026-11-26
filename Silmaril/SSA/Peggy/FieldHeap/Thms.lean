module

public import Silmaril.SSA.Peggy.FieldHeap.Defs
import Silmaril.Proofs.SSA.Peggy.FieldHeap.Rules

/-! # Field rules that preserve the heap token and first fault -/

public section

namespace Silmaril.SSA.Peggy.FieldHeap

variable {state : State} {receiver : Receiver} {field : Field}

theorem locate_ok_iff {id : ObjectId} {fields : Object} {old : Int} :
    state.locate receiver field = .ok ⟨id, fields, old⟩ ↔
      receiver = .object id ∧ state.fault = none ∧ state.heap id = some fields ∧
        fields field = some old := Proofs.locate_ok_iff

/-- A load may set the first fault but leaves the heap intact. -/
theorem getField_heap (state : State) (receiver : Receiver) (field : Field) :
    (getField state receiver field).state.heap = state.heap := by
  unfold getField
  cases state.locate receiver field <;> rfl

theorem getField_of_fault {fault : Fault} (failed : state.fault = some fault) :
    getField state receiver field = ⟨state, none⟩ := by
  rcases state with ⟨heap, status⟩
  change status = some fault at failed
  cases failed; rfl

theorem setField_of_fault {fault : Fault} (failed : state.fault = some fault) (value : Int) :
    setField state receiver field value = state := by
  rcases state with ⟨heap, status⟩
  change status = some fault at failed
  cases failed; rfl

/-- Forwarding retains the post-store token. Either the store made the field available
or the token retains its fault and suppresses the forwarded value. -/
theorem getField_setField (state : State) (receiver : Receiver) (field : Field) (value : Int) :
    getField (setField state receiver field value) receiver field =
      forwardRead (setField state receiver field value) value :=
  Proofs.getField_setField state receiver field value

/-- The plain value law of Appendix A.1 holds exactly on accessible cells. -/
theorem getField_setField_value_iff (state : State) (receiver : Receiver) (field : Field) (value : Int) :
    (getField (setField state receiver field value) receiver field).value = some value ↔
      Accessible state receiver field :=
  Proofs.getField_setField_value_iff state receiver field value

/-- A successful write at a disjoint address preserves the read's value and fault.
The read's final heap is the one produced by the write. -/
theorem getField_setField_disjoint (allowed : Accessible state receiver field) (value : Int)
    {other : Receiver} {read : Field} (disjoint : Disjoint other read receiver field) :
    getField (setField state receiver field value) other read =
      { getField state other read with
        state := { (getField state other read).state with heap := (setField state receiver field value).heap } } :=
  Proofs.getField_setField_disjoint allowed value disjoint

/-- Two adjacent writes to the same address retain only the last value, or the first fault
if the address was inaccessible. Both proposed values are already defined. -/
theorem setField_setField (state : State) (receiver : Receiver) (field : Field) (first last : Int) :
    setField (setField state receiver field first) receiver field last =
      setField state receiver field last :=
  Proofs.setField_setField state receiver field first last

/-- Observing a completed read retains its entire state and optional value. -/
theorem ordered_injective : Function.Injective ReadResult.ordered := Proofs.ordered_injective

end Silmaril.SSA.Peggy.FieldHeap
