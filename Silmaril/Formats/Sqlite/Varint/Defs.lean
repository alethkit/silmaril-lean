module
public import Silmaril.Formats.Sqlite.File.Defs

/-! SQLite varints use seven bits in each of the first eight octets and all
eight bits in a ninth octet. Overlong encodings are readable; the encoder
chooses the shortest representation, including nine octets for high values. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.Varint

def readAux? (view : File.View) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | 1, offset, acc => do
    let byte ← view.get? offset
    pure (acc * 256 + byte.toNat, offset + 1)
  | fuel + 2, offset, acc => do
    let byte ← view.get? offset
    let value := acc * 128 + byte.toNat % 128
    if byte.toNat < 128 then pure (value, offset + 1)
    else readAux? view (fuel + 1) (offset + 1) value

def readNat? (view : File.View) (offset : Nat) : Option (Nat × Nat) :=
  readAux? view 9 offset 0

def read? (view : File.View) (offset : Nat) : Option (UInt64 × Nat) :=
  (readNat? view offset).map (fun (value, next) => (UInt64.ofNat value, next))

def seven : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n => if n < 128 then [UInt8.ofNat n]
    else seven fuel (n / 128) ++ [UInt8.ofNat (n % 128 + 128)]

/-- Form the normal one-to-eight byte sequence by setting the continuation
bit on all digits except the final digit. -/
def encode (n : UInt64) : Bytes :=
  let value := n.toNat
  if value < 2^56 then
    let digits := seven 8 value
    Silmaril.Formats.Bytes.ofList ((digits.zipIdx).map fun (byte,i) =>
      if i + 1 < digits.length then UInt8.ofNat (byte.toNat % 128 + 128)
      else UInt8.ofNat (byte.toNat % 128))
  else
    Silmaril.Formats.Bytes.ofList
      ((List.range 8).map (fun i => UInt8.ofNat (value / 2^(8+7*(7-i)) % 128 + 128)) ++
        [UInt8.ofNat (value % 256)])

end Silmaril.Formats.Sqlite.Varint
