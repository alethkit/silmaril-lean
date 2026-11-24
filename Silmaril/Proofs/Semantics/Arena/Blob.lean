module

public import Silmaril.Semantics.Arena.Blob.Defs

public section

namespace Silmaril.Semantics.Arena.Blob.Proofs

open Silmaril.Semantics.Arena.Blob.State

variable {Claim Key Store Error : Type}
variable {state next : State Claim Key Store} {id : Id}

theorem allocate_fresh {value : Entry Claim}
    (success : allocate (Error := Error) value state = .ok (id, next)) :
    id.owner = state.owner ∧ id.index.val = state.slots.size ∧
    state.slots.size < state.limit ∧ next.slots.size = state.slots.size + 1 ∧
    next.slots[id.index.val]? = some (some value) ∧
    (∀ other, other ≠ id.index.val → next.slots[other]? = state.slots[other]?) ∧
    next.bindings = state.bindings ∧ next.store = state.store := by
  unfold allocate at success
  split at success
  · rename_i inside
    cases success
    refine ⟨rfl, rfl, Nat.lt_of_lt_of_le inside (Nat.min_le_left ..), by simp, by simp, ?_, rfl, rfl⟩
    intro other different
    simp [Array.getElem?_push, different]
  · contradiction

theorem remove_effect (success : remove (Error := Error) id state = .ok ((), next)) :
    next.slots.size = state.slots.size ∧ entry (Error := Error) next id = .error .stale ∧
    (∀ other, other ≠ id.index.val → next.slots[other]? = state.slots[other]?) ∧
    next.bindings = state.bindings ∧ next.store = state.store := by
  unfold remove at success
  cases entryEq : entry (Error := Error) state id with
  | error fault => simp [entryEq, bind, Except.bind] at success
  | ok value =>
    simp [entryEq, bind, Except.bind, pure, Except.pure] at success
    subst next
    have owner : id.owner = state.owner := by
      by_contra different
      simp [entry, different] at entryEq
    refine ⟨by simp, ?_, ?_, rfl, rfl⟩
    · by_cases inside : id.index.val < state.slots.size <;>
        simp [entry, owner, inside]
    · intro other different
      exact Array.getElem?_setIfInBounds_ne (Ne.symm different)

theorem lookup_min [DecidableEq Key] (profile : Profile Claim Key) {claim : Claim} {key : Key}
    (supported : profile.key? claim = some key)
    (hit : lookup (Error := Error) profile claim state = .ok (some id)) :
    id.owner = state.owner ∧
    ∃ inside : id.index.val < state.slots.size,
      registeredKey profile (state.slots[id.index.val]'inside) = some key ∧
      ∀ j (earlier : j < id.index.val),
        registeredKey profile (state.slots[j]'(Nat.lt_trans earlier inside)) ≠ some key := by
  unfold lookup at hit
  rw [supported] at hit
  cases scan : state.slots.findIdx? (fun slot => decide (registeredKey profile slot = some key)) with
  | none => simp [scan, pure, Except.pure] at hit
  | some index =>
    simp only [scan] at hit
    split at hit
    · simp [pure, Except.pure] at hit
      subst id
      obtain ⟨inside, matched, first⟩ := Array.findIdx?_eq_some_iff_getElem.mp scan
      exact ⟨rfl, inside, of_decide_eq_true matched, fun j h eq => first j h (decide_eq_true eq)⟩
    · contradiction

theorem lookup_registered [DecidableEq Key] (profile : Profile Claim Key) {claim : Claim}
    {key : Key} {index : Nat} (supported : profile.key? claim = some key)
    (bounded : state.slots.size ≤ slotCount)
    (registered : state.slots[index]? = some (some (.named claim))) :
    ∃ representative, lookup (Error := Error) profile claim state = .ok (some representative) := by
  cases scan : state.slots.findIdx? (fun slot => decide (registeredKey profile slot = some key)) with
  | none =>
    have absent := Array.of_findIdx?_eq_none scan index
    simp [registered, registeredKey, supported] at absent
  | some chosen =>
    have inside := Nat.lt_of_lt_of_le (Array.findIdx?_eq_some_iff_findIdx_eq.mp scan).1 bounded
    exact ⟨⟨state.owner, ⟨chosen, inside⟩⟩, by simp [lookup, supported, scan, inside, pure, Except.pure]⟩

theorem fetch_verified (profile : Profile Claim Key) (backing : Backing Store Key Error)
    {store : Store} {key : Key} {bytes : ByteArray}
    (success : fetch profile backing store key = .ok (some bytes)) :
    backing.get store key = .ok (some bytes) ∧ profile.verifies key bytes = true := by
  unfold fetch at success
  cases answer : backing.get store key with
  | error reason => simp [answer, Except.mapError, bind, Except.bind] at success
  | ok response =>
    cases response with
    | none => simp [answer, Except.mapError, bind, Except.bind, pure, Except.pure] at success
    | some data =>
      by_cases good : profile.verifies key data = true
      · simp [answer, Except.mapError, bind, Except.bind, pure, Except.pure, good] at success
        subst bytes
        exact ⟨rfl, good⟩
      · simp [answer, Except.mapError, bind, Except.bind, good] at success

theorem admit_effect [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    {key : Key} {bytes : ByteArray}
    (success : admit profile backing key bytes state = .ok ((), next)) :
    profile.verifies key bytes = true ∧
    (next.binding key).map Binding.bytes = some bytes ∧
    next.slots = state.slots ∧ next.store = state.store := by
  have checked (mode : Residency) :
      ((state.setBinding key ⟨bytes, mode⟩).binding key).map Binding.bytes = some bytes := by
    simp [binding, setBinding]
  by_cases good : profile.verifies key bytes = true
  · refine ⟨good, ?_⟩
    simp only [admit, good, Bool.not_true, Bool.false_eq_true, ite_false] at success
    cases prior : state.binding key with
    | some value =>
      by_cases same : bytes = value.bytes
      · simp [prior, same, pure, Except.pure] at success
        subst next
        simp [prior, same]
      · simp [prior, same] at success
    | none =>
      cases answer : fetch profile backing state.store key with
      | error reason => simp [prior, answer, bind, Except.bind] at success
      | ok response =>
        cases response with
        | none =>
          simp [prior, answer, bind, Except.bind, pure, Except.pure] at success
          subst next
          exact ⟨checked .local, rfl, rfl⟩
        | some data =>
          by_cases same : bytes = data
          · simp [prior, answer, bind, Except.bind, pure, Except.pure, same] at success
            subst next
            subst data
            exact ⟨checked _, rfl, rfl⟩
          · simp [prior, answer, bind, Except.bind, same] at success
  · simp [admit, Bool.eq_false_of_not_eq_true good] at success

theorem getMut_observation [DecidableEq Key] (profile : Profile Claim Key)
    (backing : Backing Store Key Error) (policy : Policy) (claim : Claim) :
    (getMut profile backing policy claim state).map Prod.fst = State.get profile backing state claim := by
  unfold getMut State.get
  cases profile.key? claim with
  | none => rfl
  | some key =>
    cases result : getKey profile backing state key <;>
      simp [result, bind, Except.bind, pure, Except.pure, Except.map]

theorem evict_read [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    {key : Key} {bytes : ByteArray}
    (warm : state.binding key = some ⟨bytes, .warm⟩)
    (reload : fetch profile backing state.store key = .ok (some bytes)) :
    getKey profile backing (state.setBinding key ⟨bytes, .cold⟩) key =
      getKey profile backing state key := by
  have cold : (state.setBinding key ⟨bytes, .cold⟩).binding key = some ⟨bytes, .cold⟩ := by
    simp [binding, setBinding]
  have sameStore : (state.setBinding key ⟨bytes, .cold⟩).store = state.store := rfl
  simp [getKey, warm, cold, sameStore, reload, bind, Except.bind, pure, Except.pure]

end Silmaril.Semantics.Arena.Blob.Proofs
