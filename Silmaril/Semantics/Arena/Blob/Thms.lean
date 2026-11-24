module

public import Silmaril.Semantics.Arena.Blob.Defs
import Silmaril.Proofs.Semantics.Arena.Blob

public section

namespace Silmaril.Semantics.Arena.Blob

open Silmaril.Semantics.Arena.Blob.State

variable {Claim Key Store Error : Type}
variable {state next : State Claim Key Store} {id : Id}

theorem allocate_fresh {value : Entry Claim}
    (success : allocate (Error := Error) value state = .ok (id, next)) :
    id.owner = state.owner ∧ id.index.val = state.slots.size ∧
    state.slots.size < state.limit ∧ next.slots.size = state.slots.size + 1 ∧
    next.slots[id.index.val]? = some (some value) ∧
    (∀ other, other ≠ id.index.val → next.slots[other]? = state.slots[other]?) ∧
    next.bindings = state.bindings ∧ next.store = state.store :=
  Proofs.allocate_fresh success

theorem remove_effect (success : remove (Error := Error) id state = .ok ((), next)) :
    next.slots.size = state.slots.size ∧ entry (Error := Error) next id = .error .stale ∧
    (∀ other, other ≠ id.index.val → next.slots[other]? = state.slots[other]?) ∧
    next.bindings = state.bindings ∧ next.store = state.store :=
  Proofs.remove_effect success

theorem lookup_min [DecidableEq Key] (profile : Profile Claim Key) {claim : Claim} {key : Key}
    (supported : profile.key? claim = some key)
    (hit : lookup (Error := Error) profile claim state = .ok (some id)) :
    id.owner = state.owner ∧
    ∃ inside : id.index.val < state.slots.size,
      registeredKey profile (state.slots[id.index.val]'inside) = some key ∧
      ∀ j (earlier : j < id.index.val),
        registeredKey profile (state.slots[j]'(Nat.lt_trans earlier inside)) ≠ some key :=
  Proofs.lookup_min profile supported hit

theorem lookup_registered [DecidableEq Key] (profile : Profile Claim Key) {claim : Claim}
    {key : Key} {index : Nat} (supported : profile.key? claim = some key)
    (bounded : state.slots.size ≤ slotCount)
    (registered : state.slots[index]? = some (some (.named claim))) :
    ∃ representative, lookup (Error := Error) profile claim state = .ok (some representative) :=
  Proofs.lookup_registered profile supported bounded registered

theorem fetch_verified (profile : Profile Claim Key) (backing : Backing Store Key Error)
    {store : Store} {key : Key} {bytes : ByteArray}
    (success : fetch profile backing store key = .ok (some bytes)) :
    backing.get store key = .ok (some bytes) ∧ profile.verifies key bytes = true :=
  Proofs.fetch_verified profile backing success

theorem admit_effect [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    {key : Key} {bytes : ByteArray}
    (success : admit profile backing key bytes state = .ok ((), next)) :
    profile.verifies key bytes = true ∧
    (next.binding key).map Binding.bytes = some bytes ∧
    next.slots = state.slots ∧ next.store = state.store :=
  Proofs.admit_effect profile backing success

theorem getMut_observation [DecidableEq Key] (profile : Profile Claim Key)
    (backing : Backing Store Key Error) (policy : Policy) (claim : Claim) :
    (getMut profile backing policy claim state).map Prod.fst = State.get profile backing state claim :=
  Proofs.getMut_observation profile backing policy claim

theorem evict_local [DecidableEq Key] {key : Key} {bytes : ByteArray}
    (localBinding : state.binding key = some ⟨bytes, .local⟩) :
    evict (Error := Error) key state = .error .pinned := by
  simp [evict, localBinding]

theorem evict_read [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    {key : Key} {bytes : ByteArray}
    (warm : state.binding key = some ⟨bytes, .warm⟩)
    (reload : fetch profile backing state.store key = .ok (some bytes)) :
    getKey profile backing (state.setBinding key ⟨bytes, .cold⟩) key =
      getKey profile backing state key :=
  Proofs.evict_read profile backing warm reload

end Silmaril.Semantics.Arena.Blob
