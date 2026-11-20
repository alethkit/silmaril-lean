module

import Silmaril.Formats.Dasl.NameLinkSet.Thms
meta import Silmaril.Formats.Dasl.NameLinkSet.Thms

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.NameLinkSet Silmaril.Formats.Cbor Silmaril.Semantics

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect {Value : Type} (option : Option Value) (label : String) : IO Value :=
  match option with
  | some value => pure value
  | none => throw (IO.userError label)

private def generic : IO Unit := do
  let tagged := normalize [taggedKey (.blob 3), taggedKey (.obj 3), taggedKey (.obj 3)]
  check (decide (links mixedKey tagged = [.obj 3, .blob 3])) "same abstract name, distinct tags"
  let lenient : Encode.TotalCodec Nat (Link Nat) :=
    ⟨Link.obj, (fun | .obj name => some name | .blob name => some name), fun _ => rfl⟩
  check ((codec lenient).decode? (linkArray.encode [.blob 3])).isNone "reject silent identity substitution"
  let layout := normalize [9, 2, 6, 4, 4, 1, 20]
  let idx := index layout
  for query in List.range 22 do
    check (idx.contains query == decide (query ∈ layout.keys)) "binary search edges and gaps"
  check (!(index (normalize ([] : List Nat))).contains 0) "empty index"

private def fixtures (format : Drisl.CidProfile) (hashCode : UInt8) (profile : Wire.Profile (Drisl.Cid format)) :
    IO Unit :=
  letI := cidOrder (format := format); do
  let cid kind digest := expect ((Drisl.Cid.codec format).parse?
    ([1, kind, hashCode, 32] ++ List.replicate 32 digest)) "fixture CID"
  let primary ← cid 0x71 1
  let otherName ← cid 0x71 2
  let missing ← cid 0x71 3
  let invalid ← cid 0x71 4
  let nonmember ← cid 0x71 5
  let blob ← cid 0x55 0
  let objectWire := cidWireCodec profile objectKey
  let blobWire := cidWireCodec profile blobKey
  let mixedWire := cidWireCodec profile mixedKey
  let objects := normalize [missing, otherName, primary, primary, invalid]
  let blobs := normalize [blob, blob]
  let mixed := normalize [taggedKey (.blob blob), taggedKey (.obj invalid), taggedKey (.obj primary)]
  check (decide (objects.keys = [primary, otherName, missing, invalid])) "sort and dedup by CID"
  let objectBytes ← expect (objectWire.encode? objects) "object set encodes"
  let blobBytes ← expect (blobWire.encode? blobs) "blob set encodes"
  let mixedBytes ← expect (mixedWire.encode? mixed) "mixed set encodes"
  check (decide ((objectWire.decode? objectBytes).map OrderedMap.keys = some objects.keys)) "object recovery"
  check (decide ((blobWire.decode? blobBytes).map OrderedMap.keys = some blobs.keys)) "blob recovery"
  check (decide ((mixedWire.decode? mixedBytes).map OrderedMap.keys = some mixed.keys)) "mixed recovery"
  check ((objectWire.decode? blobBytes).isNone && (blobWire.decode? objectBytes).isNone) "reject other tag"
  check ((objectWire.encode? (normalize [blob])).isNone && (blobWire.encode? (normalize [primary])).isNone)
    "wrong CID kind cannot serialize"
  for bad in [[Link.obj otherName, .obj primary], [.obj primary, .obj primary]] do
    let badBytes ← expect (profile.render? (linkArray.encode bad)) "malformed set fixture is legal wire"
    check (objectWire.decode? badBytes).isNone "reject reverse order and duplicate names"
  let raw : ByteArray := ⟨#[255, 0]⟩
  let read := wireReader profile Wire.linkSupported Encode.bits (fun name =>
    if name = primary ∨ name = otherName then some ⟨#[7]⟩
    else if name = blob ∨ name = invalid then some raw else none)
  let idx := index objects
  check (decide (idx.lookup objectKey read primary = some (.found (.inl 7)))) "object positive"
  check (decide (idx.lookup objectKey read otherName = some (.found (.inl 7)))) "aliases are distinct members"
  check (decide ((index blobs).lookup blobKey read blob = some (.found (.inr raw)))) "raw blob positive"
  check (decide ((index mixed).lookup mixedKey read (taggedKey (.blob blob)) = some (.found (.inr raw)))) "mixed blob"
  check (decide (idx.lookup objectKey read missing = some .missing)) "member with missing bytes"
  check (decide (idx.lookup objectKey read invalid = some .invalid)) "member with invalid object"
  check (decide (idx.lookup objectKey read nonmember = none)) "not indexed"
  check (decide (idx.lookup objectKey (fun _ => Resolution.unresolved (Value := Unit)) primary = some .unresolved))
    "unattempted resolution"
  let semantic : Finset UInt64 := {7}
  let preferred ← expect (objectWire.encode? (ofContents (fun _ => primary) semantic)) "first policy encodes"
  let alternate ← expect (objectWire.encode? (ofContents (fun _ => otherName) semantic)) "second policy encodes"
  check (decide (preferred ≠ alternate)) "same content under two coherent choices, different wire layouts"

public def main : IO Unit := do
  generic
  fixtures .dasl 0x12 Wire.Profile.dasl
  fixtures .bdasl 0x1e Wire.Profile.bdasl
