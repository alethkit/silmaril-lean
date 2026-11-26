module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Thms
public import Silmaril.Languages.Starlark.Lists.Iteration.Thms
public import Silmaril.Languages.Starlark.Lists.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (globalSlot enter)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (Address Capture Cell Contents State Slot Heap Outcome)
open Silmaril.Languages.Starlark.Lists.Iteration

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value

/-- All declared globals have live, distinct binding cells throughout the
setup and wrapper portion. The values inside them can change. -/
structure ModuleSlots (globals : List String) (state : State) : Prop where
  distinct : RootCall.DistinctOwned state
  usable : ∀ name ∈ globals, ∃ address value frozen,
    state.slots (globalSlot name) = some (.owned address) ∧ state.heap[address]? = some ⟨.binding value, frozen⟩

theorem entered_slots {commands : List Command} {globals : List String} {linked : Program}
    {resolved : ResolvedModule} (declared : ModuleBinders commands globals)
    (checked : resolve commands linked = .ok resolved) (caller : State) :
    ModuleSlots globals (enter resolved.source caller) := by
  refine ⟨RootCall.enter_distinct _ _, ?_⟩
  intro name member
  obtain ⟨address, slot, contents⟩ := Entry.checked_global_cell declared checked caller name member
  exact ⟨address, none, false, slot, contents⟩

theorem slots_write (state : State) (binding : Binding) (value : Value) :
    (state.write binding value).slots = state.slots := by
  unfold State.write
  split <;> try rfl
  split <;> rfl

theorem writes_binding (state : State) (target : Binding) (value : Value) (address : Address)
    (slot : state.slots target = some (.owned address)) {previous : Option Value} {frozen : Bool}
    (cell : state.heap[address]? = some ⟨.binding previous, frozen⟩) :
    (state.write target value).bindingValue target = .ok value := by
  have within := (Array.getElem?_eq_some_iff.mp cell).choose
  have updated : state.write target value =
      { state with heap := state.heap.setIfInBounds address ⟨.binding (some value), frozen⟩ } := by
    simp only [State.write, slot, cell]
  rw [updated]
  simp [State.bindingValue, slot, Slot.address, within]

theorem write_keeps_function (state : State) (target : Binding) (value : Value) (address : Address)
    (closure : Silmaril.Languages.Starlark.Lists.Closure) (frozen : Bool)
    (cell : state.heap[address]? = some ⟨.function closure, frozen⟩) :
    (state.write target value).heap[address]? = some ⟨.function closure, frozen⟩ := by
  unfold State.write
  split <;> try exact cell
  rename_i other slot
  by_cases same : other = address
  · subst other
    simp [cell]
  · split <;> simp [same, cell]

theorem written_slots {globals : List String} {state : State} (layout : ModuleSlots globals state)
    (target : Binding) (value : Value) : ModuleSlots globals (state.write target value) := by
  have unchanged := slots_write state target value
  refine ⟨by simpa only [RootCall.DistinctOwned, unchanged] using layout.distinct, ?_⟩
  intro name member
  obtain ⟨address, previous, frozen, slot, cell⟩ := layout.usable name member
  refine ⟨address, ?_⟩
  simp only [unchanged, slot, true_and]
  unfold State.write
  split <;> try exact ⟨_, _, cell⟩
  rename_i other written
  split <;> try exact ⟨_, _, cell⟩
  by_cases same : other = address
  · subst other
    have within := (Array.getElem?_eq_some_iff.mp cell).choose
    rename_i storedValue storedFrozen stored
    exact ⟨some value, storedFrozen, by simp [within]⟩
  · exact ⟨previous, frozen, by simp [same, cell]⟩

theorem retains_slots {globals : List String} {state next : State}
    (layout : ModuleSlots globals state) (slots : next.slots = state.slots)
    (cells : ∀ index, index < state.heap.size → next.heap[index]? = state.heap[index]?) :
    ModuleSlots globals next := by
  refine ⟨by simpa only [RootCall.DistinctOwned, slots] using layout.distinct, ?_⟩
  intro name member
  obtain ⟨address, previous, frozen, owned, cell⟩ := layout.usable name member
  exact ⟨address, previous, frozen, slots ▸ owned,
    (cells address (Array.getElem?_eq_some_iff.mp cell).choose).trans cell⟩

theorem retain_read {state next : State} {name : String} {address : Address}
    (owned : state.slots (globalSlot name) = some (.owned address))
    (slots : next.slots = state.slots) (cell : next.heap[address]? = state.heap[address]?) :
    next.bindingValue (globalSlot name) = state.bindingValue (globalSlot name) := by
  simp [State.bindingValue, slots, owned, Slot.address, cell]

theorem push_keeps {globals : List String} {state : State} (layout : ModuleSlots globals state)
    (cell : Cell) : ModuleSlots globals { state with heap := state.heap.push cell } :=
  retains_slots layout rfl (fun _ yes => by simp [Array.getElem?_push, Nat.ne_of_lt yes])

theorem push_live {state : State} {name : String} {address id : Nat} {captures : List Capture} {frozen : Bool}
    (live : RootCall.Live state name address id captures frozen)
    {globals : List String} (layout : ModuleSlots globals state) (member : name ∈ globals) (cell : Cell) :
    RootCall.Live { state with heap := state.heap.push cell } name address id captures frozen := by
  obtain ⟨slot, _, _, owned, stored⟩ := layout.usable name member
  have keep (index : Nat) (inside : index < state.heap.size) :
      (state.heap.push cell)[index]? = state.heap[index]? := by
    simp [Array.getElem?_push, Nat.ne_of_lt inside]
  exact ⟨live.owned,
    (retain_read (next := { state with heap := state.heap.push cell }) owned rfl (keep slot (Array.getElem?_eq_some_iff.mp stored).choose)).trans live.binding,
    (keep address (Array.getElem?_eq_some_iff.mp live.cell).choose).trans live.cell⟩

private theorem acquire_state (value : Value) (state : State) : finishState (acquireIterator value state) = state := by
  cases value <;> simp [acquireIterator, iterationSource, map_finishState, Silmaril.Languages.Starlark.Lists.listElements,
    Silmaril.Languages.Starlark.Lists.tupleElements, Silmaril.Languages.Starlark.Lists.dictEntries,
    projectCell_finishState] <;> rfl

private theorem unpack_state (value : Value) (state : State) :
    finishState (unpackValue 2 value state) = state := by
  have unchanged := acquire_state value state
  unfold unpackValue
  cases h : acquireIterator value state with
  | error error final => simpa only [h, finishState] using unchanged
  | ok result final =>
    rcases result with ⟨guard, cursor⟩
    rw [h] at unchanged
    change final = state at unchanged
    by_cases length : cursor.remaining = 2 <;> simpa [length, finishState] using unchanged

theorem leaf_total (plan : Plan) (state : State) : ∃ out, Leaf.Runs plan state out := by
  cases read : state.bindingValue plan.rhs with
  | error error => exact ⟨_, .rhsError read⟩
  | ok rhs =>
    have unchanged := unpack_state rhs state
    cases h : unpackValue 2 rhs state with
    | error error final =>
      rw [h] at unchanged
      change final = state at unchanged
      subst final
      exact ⟨_, .unpackError read ((unpacksValue_iff_unpackValue _ _ _ _).mpr h)⟩
    | ok values final =>
      rw [h] at unchanged
      change final = state at unchanged
      subst final
      have received := (unpacksValue_iff_unpackValue _ _ _ _).mpr h
      have arity := unpacksValue_length received
      match values with
      | [first, second] => exact ⟨_, .leaves read received⟩
      | [] | [_] | _ :: _ :: _ :: _ => simp at arity

private theorem globals_total (state : State) (globals : List String) : ∃ values, Leaf.Globals state globals values := by
  induction globals with
  | nil => exact ⟨[], .nil⟩
  | cons name rest ih =>
    obtain ⟨values, collected⟩ := ih
    cases h : state.bindingValue (globalSlot name) with
    | error => exact ⟨values, .absent h collected⟩
    | ok value => exact ⟨(name, value) :: values, .initialized h collected⟩

theorem publication_total (globals : List String) (caller : State) (out : Silmaril.Languages.Starlark.Modules.Result Unit) :
    ∃ observed, Finishes globals caller out observed := by
  cases out with
  | error error final => exact ⟨_, .failed⟩
  | ok _ state =>
    obtain ⟨values, collected⟩ := globals_total state globals
    exact ⟨_, .published collected ((Silmaril.Languages.Starlark.Lists.freezes_iff_freeze _ _ _).mpr rfl)⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace
