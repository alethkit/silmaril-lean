module

import Silmaril.Semantics.Arena.Blob.Thms
import Batteries.Data.Except
meta import Silmaril.Semantics.Arena.Blob.Defs
meta import Silmaril.Semantics.Arena.Mutable.Defs
meta import Batteries.Data.Except

namespace Silmaril.Semantics.Arena.Blob.Examples

open Silmaril.Semantics.Arena.Blob.State

private structure Address where
  lane : Nat
  digest : Nat
  codec : Bool
  deriving DecidableEq

private abbrev Key := Nat × Nat

private def raw : Address := ⟨0, 0, false⟩
private def labelled : Address := ⟨0, 0, true⟩
private def otherLane : Address := ⟨1, 0, false⟩
private def unsupported : Address := ⟨2, 0, false⟩

private def payload : ByteArray := ⟨#[2]⟩
private def collision : ByteArray := ⟨#[4]⟩
private def wrong : ByteArray := ⟨#[3]⟩

/-- This verifier deliberately admits both 2 and 4 for a single name. -/
private def digest (bytes : ByteArray) : Nat := (bytes[0]?.getD 0).toNat % 2

private def profile : Profile Address Key where
  key? address := if address.lane < 2 then some (address.lane, address.digest) else none
  select bytes := ⟨0, digest bytes, false⟩
  verifies key bytes := decide (key.2 = digest bytes)

private inductive Store where
  | empty
  | failed
  | present (key : Key) (bytes : ByteArray)

private def backing : Backing Store Key Unit where
  get
    | .empty, _ => .ok none
    | .failed, _ => .error ()
    | .present key bytes, query => .ok (if key = query then some bytes else none)
  retains _ _ := true
  putExact := some fun store key bytes =>
    match store with
    | .empty => .ok (.present key bytes)
    | .failed => .error (.backend ())
    | .present prior exact =>
      if prior = key ∧ exact = bytes then .ok store else .error .conflict

private def empty : State Address Key Store := {owner := 20, store := .empty, limit := 3}

private abbrev Result (α : Type) := Except (Fault Unit) α

private def freshAndTombstones : Result (List Nat × Bool × Bool) := do
  let (first, state) ← insert payload empty
  let (second, state) ← insert payload state
  let (_, state) ← remove first state
  let (third, state) ← insert payload state
  let stale := decide (read profile backing state first = .error .stale)
  let full := match insert (Error := Unit) payload state with
    | .error .exhausted => true
    | _ => false
  return ([first.index, second.index, third.index].map Fin.val, stale, full)

#guard freshAndTombstones = .ok ([0, 1, 2], true, true)

private def aliases : Result (Bool × Bool × Bool × Bool × Bool) := do
  let (a, state) ← insert payload empty
  let unnamed ← address state a
  let noLookup ← lookup profile raw state
  let (selected, state) ← ensureAddress profile backing a state
  let (b, state) ← reserveAddress profile labelled state
  let exactClaim ← address state b
  let first ← lookup profile labelled state
  let (c, state) ← reserveAddress profile otherLane state
  let secondLane ← read profile backing state c
  let (_, state) ← remove a state
  let next ← lookup profile raw state
  let output ← read profile backing state b
  return (decide (unnamed = none ∧ noLookup = none), decide (selected = raw ∧ exactClaim = some labelled),
    decide (first = some a ∧ next = some b), decide (secondLane = none), decide (output = some payload))

#guard aliases = .ok (true, true, true, true, true)

private def admission : Result (Bool × Bool × Bool × Bool × Bool) := do
  let (id, reserved) ← reserveAddress profile raw empty
  let before ← read profile backing reserved id
  let (_, filled) ← fill profile backing id payload reserved
  let (_, again) ← fill profile backing id payload filled
  let (result, after) := Mutable.Mutation.commit (importAddress profile backing labelled collision) again
  let (duplicate, repeated) ← importAddress profile backing labelled payload after
  let found ← read profile backing repeated id
  return (decide (before = none), decide (result = .error .conflict),
    decide (after.slots.size = 1 ∧ duplicate.index.val = 1),
    decide (found = some payload), (match fill profile backing id wrong filled with | .error .rejected => true | _ => false))

#guard admission = .ok (true, true, true, true, true)

private def publishByAddress : Result (Bool × Bool × Bool × Bool) := do
  let (cid, state) ← put profile backing payload empty
  let registration ← lookup profile cid state
  let (stored, persisted) ← persist profile backing cid state
  let reloaded ← State.get profile backing persisted cid
  let pinned := match evict (Error := Unit) (0, 0) state with
    | .error .pinned => true
    | _ => false
  return (decide (registration = none ∧ state.slots.size = 0),
    pinned, stored, decide (reloaded = some payload))

#guard publishByAddress = .ok (true, true, true, true)

private def cache : Result (List Nat × Bool × Bool) := do
  let (id, state) ← reserveAddress profile raw {empty with store := .present (0, 0) payload}
  let (coldRead, cold) ← readMut profile backing (.maxBytes 0) id state
  let (warmRead, warm) ← readMut profile backing (.maxBytes 1) id cold
  let (_, evicted) ← evict (0, 0) warm
  let warmDuringFailure := State.get profile backing {warm with store := .failed} raw
  let coldDuringFailure := State.get profile backing {evicted with store := .failed} raw
  let coldCollision := State.get profile backing {evicted with store := .present (0, 0) collision} raw
  return ([state.cachedBytes, cold.cachedBytes, warm.cachedBytes, evicted.cachedBytes],
    decide (coldRead = some payload ∧ warmRead = some payload ∧ warmDuringFailure = .ok (some payload)),
    decide (coldDuringFailure = .error (.backend ()) ∧ coldCollision = .error .corrupt))

#guard cache = .ok ([0, 0, 1, 0], true, true)

private def failedRead : Result (Bool × Bool × Bool × Bool × Bool × Bool) := do
  let (id, state) ← reserveAddress profile raw {empty with store := .present (0, 0) wrong}
  let (result, unchanged) :=
    Mutable.Mutation.commit (readMut profile backing (.maxBytes 1) id) state
  let foreign := read profile backing state {id with owner := 21}
  let unsupportedRead := State.get profile backing state unsupported
  let (putResult, afterPut) := Mutable.Mutation.commit (put profile backing payload) state
  return (decide (result = .error .corrupt), decide (unchanged.cachedBytes = 0), decide (foreign = .error .foreign),
    decide (unsupportedRead = .error .unsupported), decide (putResult = .error .corrupt),
    decide (afterPut.bindings.length = 0))

#guard failedRead = .ok (true, true, true, true, true, true)

end Silmaril.Semantics.Arena.Blob.Examples
