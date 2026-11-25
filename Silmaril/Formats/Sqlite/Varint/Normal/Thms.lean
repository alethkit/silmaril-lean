module

public import Silmaril.Formats.Sqlite.Varint.Defs
import Silmaril.Proofs.Formats.Sqlite.Varint.Normal.Roundtrip

public section
namespace Silmaril.Formats.Sqlite.Varint

/-- The normal SQLite encoder emits the exact base-128 width. Zero uses one octet. -/
theorem encode_width_normal (value : UInt64) (width : Nat)
    (positive : 0 < width) (enough : width ≤ 8)
    (lo : width = 1 ∨ 128 ^ (width - 1) ≤ value.toNat)
    (hi : value.toNat < 128 ^ width) : (encode value).toList.length = width :=
  Silmaril.Proofs.Formats.Sqlite.Varint.Normal.encode_width value width positive enough lo hi

/-- Given the emitted bytes at an arbitrary view offset, the normal decoder
recovers the exact value and stops immediately after its one to eight octets. -/
theorem read?_encode_normal (view : File.View) (offset : Nat) (value : UInt64) (width : Nat)
    (positive : 0 < width) (enough : width ≤ 8)
    (lo : width = 1 ∨ 128 ^ (width - 1) ≤ value.toNat)
    (hi : value.toNat < 128 ^ width)
    (bytes : ∀ i, i < width → view.get? (offset + i) = (encode value).toList[i]?) :
    read? view offset = some (value, offset + width) :=
  Silmaril.Proofs.Formats.Sqlite.Varint.Normal.read_encode_normal
    view offset value width positive enough lo hi bytes

end Silmaril.Formats.Sqlite.Varint
