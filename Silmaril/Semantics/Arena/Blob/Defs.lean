module

public import Silmaril.Semantics.Arena.Mutable.Defs
public import Init.Data.Array.Find

@[expose] public section

namespace Silmaril.Semantics.Arena.Blob

def slotCount : Nat := 2 ^ 32

/-- The owner is a model of an arena scope. The index has exactly the range of a u32. -/
structure Id where
  owner : Nat
  index : Fin slotCount
  deriving DecidableEq, Repr

/-- Classification preserves the full claim for export and selects the byte-binding
key for lookup. Verification checks bytes in the key's own domain. -/
structure Profile (Claim Key : Type) where
  key? : Claim → Option Key
  select : ByteArray → Claim
  verifies : Key → ByteArray → Bool

inductive WriteFault (Error : Type) where
  | conflict
  | backend (error : Error)

structure Backing (Store Key Error : Type) where
  get : Store → Key → Except Error (Option ByteArray)
  /-- A positive observation for this key is an exact reload anchor. -/
  retains : Store → Key → Bool := fun _ _ => false
  putExact : Option (Store → Key → ByteArray → Except (WriteFault Error) Store) := none

inductive Fault (Error : Type) where
  | foreign
  | stale
  | exhausted
  | unsupported
  | anonymous
  | rejected
  | conflict
  | corrupt
  | backingLost
  | readOnly
  | pinned
  | backend (error : Error)
  deriving DecidableEq, Repr

inductive Entry (Claim : Type) where
  | anonymous (bytes : ByteArray)
  | named (claim : Claim)

inductive Residency where
  | local
  | warm
  | cold
  deriving DecidableEq, Repr

/-- For a cold binding, exact bytes are the abstract backing witness, outside
the resident byte budget. A production backend can supply an exact immutable
snapshot guarantee instead of retaining this witness in arena memory. -/
structure Binding where
  bytes : ByteArray
  residency : Residency

structure State (Claim Key Store : Type) where
  owner : Nat
  store : Store
  limit : Nat := slotCount
  slots : Array (Option (Entry Claim)) := #[]
  bindings : List (Key × Binding) := []

/-- A policy controls positive read admission only. The implementation model
for victim selection is explicit eviction. -/
structure Policy where
  admit : Nat → Nat → Bool

def Policy.keepCold : Policy := ⟨fun _ _ => false⟩

def Policy.maxBytes (budget : Nat) : Policy :=
  ⟨fun used incoming => decide (used + incoming ≤ budget)⟩

variable {Claim Key Store Error : Type}

abbrev Edit (Claim Key Store Error Result : Type) :=
  Mutable.Mutation (State Claim Key Store) (Fault Error) Result

namespace State

def allocate (entry : Entry Claim) : Edit Claim Key Store Error Id := fun state =>
  if inside : state.slots.size < min state.limit slotCount then
    .ok (⟨state.owner, ⟨state.slots.size, Nat.lt_of_lt_of_le inside (Nat.min_le_right ..)⟩⟩,
      {state with slots := state.slots.push (some entry)})
  else .error .exhausted

def entry (state : State Claim Key Store) (id : Id) : Except (Fault Error) (Entry Claim) :=
  if id.owner ≠ state.owner then .error .foreign
  else match state.slots[id.index.val]?.join with
    | none => .error .stale
    | some value => .ok value

def remove (id : Id) : Edit Claim Key Store Error Unit := fun state => do
  let _ ← state.entry id
  return ((), {state with slots := state.slots.setIfInBounds id.index.val none})

def insert (bytes : ByteArray) : Edit Claim Key Store Error Id := allocate (.anonymous bytes)

def address (state : State Claim Key Store) (id : Id) : Except (Fault Error) (Option Claim) := do
  match ← state.entry id with
  | .anonymous _ => return none
  | .named claim => return some claim

def registeredKey (profile : Profile Claim Key) : Option (Entry Claim) → Option Key
  | some (.named claim) => profile.key? claim
  | _ => none

/-- The first live slot is the representative. The reference recomputes the
member index by scanning, independently of backing and residency. -/
def lookup [DecidableEq Key] (profile : Profile Claim Key) (claim : Claim)
    (state : State Claim Key Store) : Except (Fault Error) (Option Id) := do
  let some key := profile.key? claim | .error .unsupported
  let some index := state.slots.findIdx? (fun slot => decide (registeredKey profile slot = some key))
    | return none
  if inside : index < slotCount then return some ⟨state.owner, ⟨index, inside⟩⟩
  else .error .exhausted

def reserveAddress (profile : Profile Claim Key) (claim : Claim) : Edit Claim Key Store Error Id :=
  if (profile.key? claim).isSome then allocate (.named claim)
  else fun _ => .error .unsupported

def binding [DecidableEq Key] (state : State Claim Key Store) (key : Key) : Option Binding :=
  state.bindings.findSome? fun (other, value) => if other = key then some value else none

def setBinding [DecidableEq Key] (state : State Claim Key Store) (key : Key) (value : Binding) :
    State Claim Key Store :=
  {state with bindings := (key, value) :: state.bindings.filter (fun (other, _) => other ≠ key)}

def cachedBytes (state : State Claim Key Store) : Nat :=
  state.bindings.foldl (fun used (_, value) =>
    match value.residency with
    | .warm => used + value.bytes.size
    | _ => used) 0

def fetch (profile : Profile Claim Key) (backing : Backing Store Key Error) (store : Store)
    (key : Key) : Except (Fault Error) (Option ByteArray) := do
  match ← (backing.get store key).mapError Fault.backend with
  | none => return none
  | some bytes => if profile.verifies key bytes then return some bytes else .error .corrupt

def getKey [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (state : State Claim Key Store) (key : Key) : Except (Fault Error) (Option ByteArray) := do
  match state.binding key with
  | none => fetch profile backing state.store key
  | some value =>
    match value.residency with
    | .local | .warm => return some value.bytes
    | .cold =>
      let some bytes ← fetch profile backing state.store key | .error .backingLost
      if bytes = value.bytes then return some bytes else .error .corrupt

def get [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (state : State Claim Key Store) (claim : Claim) : Except (Fault Error) (Option ByteArray) := do
  let some key := profile.key? claim | .error .unsupported
  getKey profile backing state key

def read [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (state : State Claim Key Store) (id : Id) : Except (Fault Error) (Option ByteArray) := do
  match ← state.entry id with
  | .anonymous bytes => return some bytes
  | .named claim => get profile backing state claim

def getMut [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (policy : Policy) (claim : Claim) : Edit Claim Key Store Error (Option ByteArray) := fun state => do
  let some key := profile.key? claim | .error .unsupported
  let result ← getKey profile backing state key
  let next := match result with
    | none => state
    | some bytes =>
      let canWarm := match state.binding key with
        | none | some ⟨_, .cold⟩ => true
        | _ => false
      if canWarm && backing.retains state.store key && policy.admit state.cachedBytes bytes.size then
        state.setBinding key ⟨bytes, .warm⟩
      else state
  return (result, next)

def readMut [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (policy : Policy) (id : Id) : Edit Claim Key Store Error (Option ByteArray) := fun state => do
  match ← state.entry id with
  | .anonymous bytes => return (some bytes, state)
  | .named claim => getMut profile backing policy claim state

/-- An admitted key is immutable. With no local binding, check the backing
observation before publishing a local value. -/
def admit [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (key : Key) (bytes : ByteArray) : Edit Claim Key Store Error Unit := fun state => do
  if !profile.verifies key bytes then
    .error .rejected
  else match state.binding key with
    | some prior => if bytes = prior.bytes then return ((), state) else .error .conflict
    | none =>
      match ← fetch profile backing state.store key with
      | none => return ((), state.setBinding key ⟨bytes, .local⟩)
      | some prior =>
        if bytes = prior then
          let residency := if backing.retains state.store key then Residency.cold else .local
          return ((), state.setBinding key ⟨bytes, residency⟩)
        else .error .conflict

def put [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (bytes : ByteArray) : Edit Claim Key Store Error Claim := fun state => do
  let claim := profile.select bytes
  let some key := profile.key? claim | .error .unsupported
  let (_, next) ← admit profile backing key bytes state
  return (claim, next)

def fill [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (id : Id) (bytes : ByteArray) : Edit Claim Key Store Error Unit := fun state => do
  let some claim ← state.address id | .error .anonymous
  let some key := profile.key? claim | .error .unsupported
  admit profile backing key bytes state

def importAddress [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (claim : Claim) (bytes : ByteArray) : Edit Claim Key Store Error Id := fun state => do
  let some key := profile.key? claim | .error .unsupported
  let (id, staged) ← allocate (.named claim) state
  let (_, next) ← admit profile backing key bytes staged
  return (id, next)

def ensureAddress [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (id : Id) : Edit Claim Key Store Error Claim := fun state => do
  match ← state.entry id with
  | .named claim => return (claim, state)
  | .anonymous bytes =>
    let (claim, next) ← put profile backing bytes state
    return (claim, {next with slots := next.slots.setIfInBounds id.index.val (some (.named claim))})

/-- Persistence is explicitly requested. For a local binding, the backend must
admit the exact key and exact bytes, or return a classified failure. -/
def persist [DecidableEq Key] (profile : Profile Claim Key) (backing : Backing Store Key Error)
    (claim : Claim) : Edit Claim Key Store Error Bool := fun state => do
  let some key := profile.key? claim | .error .unsupported
  let some value := state.binding key | return (false, state)
  match value.residency with
  | .warm | .cold => return (true, state)
  | .local =>
    let some write := backing.putExact | .error .readOnly
    let store ← (write state.store key value.bytes).mapError fun
      | .conflict => Fault.conflict
      | .backend error => .backend error
    return (true, ({state with store}).setBinding key ⟨value.bytes, .cold⟩)

def evict [DecidableEq Key] (key : Key) : Edit Claim Key Store Error Bool := fun state =>
  match state.binding key with
  | some ⟨_, .local⟩ => .error .pinned
  | some ⟨bytes, .warm⟩ => .ok (true, state.setBinding key ⟨bytes, .cold⟩)
  | _ => .ok (false, state)

end State
end Silmaril.Semantics.Arena.Blob
