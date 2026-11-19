module

public import Silmaril.Formats.Cbor.Drisl.Model.Defs
public import Silmaril.Formats.JsonWire.Defs
public import Silmaril.Semantics.Naming.Defs

/-! Versioned JSON object semantics for naming, not a canonicalizer for raw RFC 8259 text.
Map order is immaterial; arrays retain order. Keys and string values are exact UTF-16 code
units. Numbers compare as exact sign/coefficient/exponent triples, not as reals or doubles. -/

@[expose] public section

namespace Silmaril.Formats.Dasl.JsonObject

open Cbor Semantics.Naming

abbrev Fields := JsonWire.Syn JsonWire.Decimal .obj

def keyLt (left right : JsonWire.Units) : Bool := left.lex right (fun first second => first < second)

def strictKeys : List JsonWire.Units → Bool
  | first :: second :: rest => keyLt first second && strictKeys (second :: rest)
  | _ => true

/-- Recursively sort maps but do not collapse duplicate keys. -/
def order : {index : JsonIx} → JsonWire.Syn JsonWire.Decimal index → JsonWire.Syn JsonWire.Decimal index
  | _, .scalar value => .scalar value
  | _, .list items => .list (order items)
  | _, .map fields => .map (.ofEntries ((order fields).toEntries.mergeSort
      (fun left right => !keyLt right.1 left.1)))
  | _, .nil => .nil
  | _, .cons item rest => .cons (order item) (order rest)
  | _, .objNil => .objNil
  | _, .objCons key value rest => .objCons key (order value) (order rest)

def ordered : {index : JsonIx} → JsonWire.Syn JsonWire.Decimal index → Bool
  | _, .scalar _ => true
  | _, .list items => ordered items
  | _, .map fields => strictKeys fields.keys && ordered fields
  | _, .nil => true
  | _, .cons item rest => ordered item && ordered rest
  | _, .objNil => true
  | _, .objCons _ value rest => ordered value && ordered rest

/-- `SJ` version 1, then the canonical representative's exact JSON printer output. The
envelope is a DRISL byte string, so arbitrary UTF-16 code units do not become CBOR text. -/
def body (fields : Fields) : List UInt8 :=
  [0x53, 0x4a, 0x01] ++ (JsonWire.encode (.map fields)).toList

def Supported (fields : Fields) : Prop :=
  ordered (.map fields) = true ∧ (body fields).length < 2 ^ 64

instance (fields : Fields) : Decidable (Supported fields) :=
  inferInstanceAs (Decidable (ordered (.map fields) = true ∧ (body fields).length < 2 ^ 64))

abbrev Object := { fields : Fields // Supported fields }

def admit? (fields : Fields) : Option Object :=
  if witness : Supported fields then some ⟨fields, witness⟩ else none

/-- Parse complete RFC JSON, then enforce the duplicate-free, bounded object profile. -/
def parse? (source : Bytes) : Option Object := do
  let .map fields ← (JsonWire.parse? source).map order | none
  admit? fields

/-- The shortest definite-length CBOR byte-string encoding used by the DRISL writer. -/
def encode (object : Object) : List UInt8 := (Value.bytes (body object.val)).encode

/-- Read the versioned envelope, checking the canonical byte representative as well as the type. -/
def decode? (bytes : List UInt8) : Option Object := do
  let .scalar (.data (.bytes (0x53 :: 0x4a :: 0x01 :: json))) ←
    Drisl.parseCbor? Drisl.i64Cbor (Drisl.Cid.codec .dasl) bytes | none
  let .map fields ← JsonWire.parse? (Bytes.ofList json) | none
  let object ← admit? fields
  if encode object = bytes then some object else none

/-- A fixed, total, single-valued byte naming convention, restricted to DASL object CIDs.
This interface does not assert that the relation computes a digest or that names are injective. -/
structure Profile where
  observe : Relation (Drisl.Cid .dasl) (List UInt8)
  objectCodec : ∀ ⦃name bytes⦄, observe name bytes → name.val[1]? = some 0x71
  coherent : UniqueNames observe
  total : ∀ bytes, ∃ name, observe name bytes

def names (profile : Profile) : Relation (Drisl.Cid .dasl) Object :=
  fun name object => profile.observe name (encode object)

end Silmaril.Formats.Dasl.JsonObject
