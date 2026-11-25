module

public import Silmaril.Formats.Sqlite.Varint.Defs
import Silmaril.Proofs.Formats.Sqlite.Varint.Exact.Read

public section
namespace Silmaril.Formats.Sqlite.Varint

/-- Reading the emitted bytes at a view offset recovers the original key. The
returned offset advances by exactly the encoded length, for every `UInt64`. -/
theorem read?_encode (view : File.View) (offset : Nat) (value : UInt64)
    (bytes : ∀ i, i < (encode value).toList.length →
      view.get? (offset + i) = (encode value).toList[i]?) :
    read? view offset = some (value, offset + (encode value).toList.length) :=
  Silmaril.Proofs.Formats.Sqlite.Varint.Exact.read_encode view offset value bytes

end Silmaril.Formats.Sqlite.Varint
