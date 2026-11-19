module

import Silmaril.Formats.Dasl.Thms
import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Formats.Dasl.Wire.Thms
meta import Silmaril.Formats.Dasl.Wire.Defs

open Silmaril.Formats.Dasl Silmaril.Semantics.Naming

private def aliases : Relation (Bool × Unit) Unit := graph (fun _ => some ())

example : Binding aliases ∧ ¬ UniqueNames aliases := by
  refine ⟨graph_binding _, fun unique => ?_⟩
  have same : ((false, ()) : Bool × Unit) = (true, ()) := unique rfl rfl
  exact Bool.noConfusion (congrArg Prod.fst same)

private def exampleStore : Store Bool :=
  ⟨graph (fun name => if name then none else some (.ref (.blob true))),
    graph (fun name => if name then some ByteArray.empty else none)⟩

example : ¬ Binding (PartialNames exampleStore) := by
  intro bound
  have opaqueHit : PartialNames exampleStore false (.ref (.blob true)) :=
    ⟨rfl, by constructor <;> intro name payload impossible <;> exact impossible.elim⟩
  have resolved : PartialNames exampleStore false (.blob true ByteArray.empty) := by
    refine ⟨rfl, ⟨?_, ?_⟩⟩
    · intro name payload impossible; exact impossible.elim
    · rintro name payload ⟨rfl, rfl⟩; rfl
  have same := bound opaqueHit resolved
  cases same

private def observations : Partial Nat :=
  .list 2 fun index =>
    .obj 0 (if index.val = 0 then .ref (.blob 1) else .blob 1 ByteArray.empty)

example : observations.LocallyBinding := by
  constructor
  · intro name left right first second
    have canonical (value : Shallow Nat) (hit : observations.bindings.objects name value) :
        value = .ref (.blob 1) := by
      obtain ⟨index, hit⟩ := hit
      change (Partial.bindings (.obj 0 (if index.val = 0 then .ref (.blob 1) else
        .blob 1 ByteArray.empty))).objects name value at hit
      split at hit <;> rcases hit with ⟨_, hit⟩ | impossible <;> first | exact hit | exact impossible.elim
    exact (canonical left first).trans (canonical right second).symm
  · intro name left right first second
    have canonical (value : ByteArray) (hit : observations.bindings.blobs name value) :
        value = ByteArray.empty := by
      obtain ⟨index, hit⟩ := hit
      change (Partial.bindings (.obj 0 (if index.val = 0 then .ref (.blob 1) else
        .blob 1 ByteArray.empty))).blobs name value at hit
      split at hit
      · exact hit.elim
      · exact hit.2
    exact (canonical left first).trans (canonical right second).symm

example : Link.blob 1 ∉ Partial.links false observations := by
  rintro ⟨_, hit⟩
  change Link.blob 1 = Link.obj 0 at hit
  cases hit

example : Link.blob 1 ∈ Partial.links true observations := ⟨0, Or.inr rfl⟩

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def roundtripI64 (bits : UInt64) (bytes : ByteArray) : IO Unit := do
  check (Wire.render? (.i64 bits) == some bytes) "signed CBOR encoding"
  match Wire.parse? bytes with
  | some (.i64 result) => check (result == bits) "signed CBOR decoding"
  | _ => throw (IO.userError "expected an i64")

public def main : IO Unit := do
  roundtripI64 0xFFFFFFFFFFFFFFFF ⟨#[0x20]⟩
  roundtripI64 0x8000000000000000 ⟨#[0x3B, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]⟩
  roundtripI64 0x7FFFFFFFFFFFFFFF ⟨#[0x1B, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]⟩
  let canonical : ByteArray := ⟨#[0xA2, 0x61, 0x62, 0xF5, 0x62, 0x61, 0x61, 0x21]⟩
  let some (.dict keys values) := Wire.parse? canonical | throw (IO.userError "expected dict")
  let inspect (key : String) := if member : key ∈ keys then values ⟨key, member⟩ else .null
  match inspect "b", inspect "aa" with
  | .bool true, .i64 bits => check (bits == 0xFFFFFFFFFFFFFFFE) "dictionary selects named fields"
  | _, _ => throw (IO.userError "dictionary field values changed")
  check (Wire.render? (.dict keys values) == some canonical) "CBOR order sorts encoded keys, not strings"
  check ((Wire.parse? ⟨#[0xA2, 0x61, 0x62, 0xF5, 0x61, 0x62, 0xF4]⟩).isNone) "duplicate key"
  check ((Wire.parse? ⟨#[0xA2, 0x62, 0x61, 0x61, 0x21, 0x61, 0x62, 0xF5]⟩).isNone) "wrong key order"
  check ((Wire.parse? ⟨#[0x18, 0x00]⟩).isNone) "overlong integer"
  check ((Wire.parse? ⟨#[0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0]⟩).isNone) "signed overflow"
  let objBytes := [1, 0x71, 0x12, 32] ++ List.replicate 32 (0 : UInt8)
  let rawBytes := [1, 0x55, 0x12, 32] ++ List.replicate 32 (0 : UInt8)
  let tag (cid : List UInt8) := ([0xD8, 0x2A, 0x58, 37, 0] ++ cid).toByteArray
  let some (.ref (.obj obj)) := Wire.parse? (tag objBytes) | throw (IO.userError "object CID")
  let some (.ref (.blob raw)) := Wire.parse? (tag rawBytes) | throw (IO.userError "raw CID")
  check (Wire.render? (.ref (.obj obj)) == some (tag objBytes)) "object CID roundtrip"
  check (Wire.render? (.ref (.blob raw)) == some (tag rawBytes)) "raw CID roundtrip"
  check ((Wire.render? (.ref (.obj raw))).isNone) "reject wrong kind"
  match Wire.readObject (fun _ => none) obj, Wire.readObject (fun _ => some ⟨#[0xFF]⟩) obj,
      Wire.readObject (fun _ => some canonical) obj, Wire.readObject (fun _ => none) raw with
  | .missing, .invalidWire, .found _, .invalidWire => pure ()
  | _, _, _, _ => throw (IO.userError "object read must distinguish missing and invalid")
