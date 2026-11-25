module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.TableLeaf.Frame.Read

public section
namespace Silmaril.Formats.Sqlite.TableLeaf

/-- Equal-length views with the same header, pointers, and content bytes
produce the same packed-leaf result, including rejection. The decoded count
and content fields identify the interval between the pointer array and cells. -/
theorem read?_gap_eq (left right : File.View) (base count content : Nat)
    (length : left.length = right.length)
    (countField : left.be? (base + 3) 2 = some count)
    (contentField : left.be? (base + 5) 2 = some content)
    (headerBytes : ∀ i, base ≤ i → i < base + 8 + 2 * count → left.get? i = right.get? i)
    (body : ∀ i, content ≤ i → i < left.length → left.get? i = right.get? i) :
    read? right base = read? left base :=
  Silmaril.Proofs.Formats.Sqlite.TableLeaf.Frame.read?_gap_eq left right base count content
    length countField contentField headerBytes body

end Silmaril.Formats.Sqlite.TableLeaf
