module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.Store
public import Silmaril.Languages.Starlark.Functions.Comprehensions.Expression.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf
open Silmaril.Languages.Starlark.Functions (enterTemporaryBindings restoreTemporaryBindings restoreCaller)
open Silmaril.Languages.Starlark.Functions.Comprehensions (patternSlot argumentSlot)

abbrev Edits := List (Binding × Option Value)

@[expose] def keys (edits : Edits) : List Binding := edits.map Prod.fst

@[expose] def patch (edits : Edits) (state : State) : State :=
  { state with bindings := fun key => (edits.lookup key).getD (state.bindings key) }

@[expose] def clear (names : List Binding) : Edits := names.map (·, none)

theorem patch_nil (state : State) : patch [] state = state := by cases state; rfl

theorem patch_append (first second : Edits) (state : State) :
    patch (first ++ second) state = patch first (patch second state) := by
  simp only [patch, List.lookup_append]
  congr 1
  funext key
  cases first.lookup key <;> rfl

theorem absent_lookup (edits : Edits) (key : Binding) (outside : key ∉ keys edits) :
    edits.lookup key = none := by
  exact List.lookup_eq_none_iff.mpr (by
    intro item member
    have different : key ≠ item.1 := fun equal => outside (List.mem_map.mpr ⟨item, member, equal.symm⟩)
    simp [bne, different])

theorem patch_outside (edits : Edits) (key : Binding) (outside : key ∉ keys edits) (state : State) :
    (patch edits state).bindings key = state.bindings key := by
  simp [patch, absent_lookup edits key outside]

theorem patch_read (edits : Edits) (key : Binding) (outside : key ∉ keys edits) (state : State) :
    (patch edits state).bindingValue key = state.bindingValue key := by
  have keep := patch_outside edits key outside state
  simp [State.bindingValue, keep, show (patch edits state).slots = state.slots from rfl,
    show (patch edits state).heap = state.heap from rfl]

theorem patch_read_found (edits : Edits) (key : Binding) (value : Value) (state : State)
    (slot : state.slots key = none) (saved : edits.lookup key = some (some value)) :
    (patch edits state).bindingValue key = .ok value := by
  simp [State.bindingValue, patch, slot, saved]

theorem private_write (edits : Edits) (state : State) (key : Binding) (value : Value)
    (slot : state.slots key = none) :
    (patch edits state).write key value = patch ((key, some value) :: edits) state := by
  simp only [State.write, patch, slot]
  congr 1
  funext binding
  by_cases same : binding = key
  · subst binding; simp
  · have different : (binding == key) = false := Bool.eq_false_iff.mpr (fun eq => same (beq_iff_eq.mp eq))
    simp [List.lookup_cons, same, different]

theorem write_fields (state : State) (key : Binding) (value : Value) :
    (state.write key value).slots = state.slots ∧
      ∀ other, other ≠ key → (state.write key value).bindings other = state.bindings other := by
  unfold State.write
  split
  · exact ⟨rfl, fun other different => by simp [different]⟩
  · exact ⟨rfl, fun _ _ => rfl⟩
  · split <;> exact ⟨rfl, fun _ _ => rfl⟩

theorem write_patch (edits : Edits) (state : State) (key : Binding) (value : Value)
    (outside : key ∉ keys edits) :
    (patch edits state).write key value = patch edits (state.write key value) := by
  have sameSlots : (patch edits state).slots = state.slots := rfl
  have sameHeap : (patch edits state).heap = state.heap := rfl
  cases slot : state.slots key with
  | none =>
    simp only [State.write, slot, patch]
    congr 1
    funext binding
    by_cases same : binding = key
    · subst binding
      simp [absent_lookup edits key outside]
    · simp [same]
  | some slotKind =>
    cases slotKind with
    | captured => simp only [State.write, sameSlots, slot]
    | owned address =>
      simp only [State.write, sameSlots, sameHeap, slot]
      cases cell : state.heap[address]? with
      | none => rfl
      | some contents =>
        cases contents with
        | mk contents frozen => cases contents <;> rfl

theorem clear_eq (names : List Binding) (state : State)
    (free : ∀ name ∈ names, state.slots name = none) :
    enterTemporaryBindings names state = patch (clear names) state := by
  have lookup (items : List Binding) (key : Binding) :
      (clear items).lookup key = if key ∈ items then some none else none := by
    induction items with
    | nil => rfl
    | cons first rest ih =>
      by_cases same : key = first
      · subst key
        simp [clear]
      · have different : (key == first) = false :=
          Bool.eq_false_iff.mpr (fun eq => same (beq_iff_eq.mp eq))
        simpa [clear, List.lookup_cons, same, different] using ih
  simp only [enterTemporaryBindings, patch]
  congr 1
  · funext key
    by_cases member : key ∈ names <;> simp [lookup names key, member]
  · funext key
    by_cases member : key ∈ names
    · simp [member, free key member]
    · simp [member]

/-- Restore the temporary coordinates. Changes elsewhere belong to the
underlying state, including writes that preceded an error. -/
theorem restore_patch (names : List Binding) (original next : State) (edits : Edits)
    (only : ∀ key ∈ keys edits, key ∈ names)
    (slots : original.slots = next.slots)
    (preserved : ∀ key ∈ names, original.bindings key = next.bindings key)
    (out : Outcome Flow) :
    (∀ (result : Flow), out = .ok result next → restoreTemporaryBindings names original
      (.ok result (patch edits next)) = out) ∧
    (∀ (error : Error), out = .error error next → restoreTemporaryBindings names original
      (.error error (patch edits next)) = out) := by
  have reset : { (patch edits next) with
      slots := fun key => if names.contains key then original.slots key else (patch edits next).slots key
      bindings := fun key => if names.contains key then original.bindings key else (patch edits next).bindings key } =
      next := by
    cases next
    simp only [patch]
    congr 1
    · funext key
      by_cases member : key ∈ names
      · simpa [member] using preserved key member
      · simp [member, absent_lookup edits key (fun present => member (only key present))]
    · funext key
      simp [slots]
  exact ⟨fun result same => by
    rw [same]
    exact congrArg (fun state => (.ok result state : Outcome Flow)) reset,
    fun error same => by
      rw [same]
      exact congrArg (fun state => (.error error state : Outcome Flow)) reset⟩

theorem private_pattern (depth index : Nat) : (patternSlot depth index).name.toList.head? = some '$' := rfl
theorem private_argument (index : Nat) : (argumentSlot index).name.toList.head? = some '$' := rfl

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf
