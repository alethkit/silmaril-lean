module

public import Silmaril.Formats.Dasl.Wire.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Formats.Dasl.Wire

public section

namespace Silmaril.Formats.Dasl.Wire

open Silmaril.Formats.Cbor Silmaril.Semantics.Naming

theorem i64_roundtrip (bits : UInt64) :
    (Drisl.i64Cbor.readNumber? (Drisl.i64Cbor.number bits.toInt64)).map Int64.toUInt64 = some bits :=
  Proofs.Formats.Dasl.i64_roundtrip bits

theorem object_raw_disjoint {name : Cid} (object : IsObjectCid name) (raw : IsRawCid name) : False :=
  (by decide : (0x71 : UInt8) ≠ 0x55) (Option.some.inj (object.symm.trans raw))

theorem codec_disjoint_domains {store : Stores Cid (Shallow Cid) ByteArray}
    (objects : ∀ ⦃name payload⦄, store.objects name payload → IsObjectCid name)
    (blobs : ∀ ⦃name payload⦄, store.blobs name payload → IsRawCid name) : store.DisjointDomains := by
  intro name obj blob object raw
  exact object_raw_disjoint (objects object) (blobs raw)

theorem serializes_binding : Binding Serializes := by
  intro value left right first second
  exact Option.some.inj (first.1.symm.trans second.1)

theorem flatten_binding {store : Stores Cid (Shallow Cid) ByteArray} (bound : store.Binding)
    (domains : store.DisjointDomains) : Binding (store.flatten Serializes) :=
  bound.flatten domains serializes_binding

theorem push_parse_iff {objects : Relation Cid (Shallow Cid)} {name wire value}
    (parsed : parse? wire = some value) :
    push objects Serializes name wire ↔ objects name value ∧ Serializes value wire :=
  Silmaril.Semantics.Naming.push_parse_iff (by intro source bytes encoded; exact encoded.2) parsed

end Silmaril.Formats.Dasl.Wire
