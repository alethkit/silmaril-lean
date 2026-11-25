module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Gap.Padding

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite

/-- A successful packed layout fills the half-open interval between the pointer
array and the cell contents with zeros. The byte slice succeeds with length zero
when the page exactly fits. Offsets include the leading bytes. -/
theorem layout_gap_slice {leading page : List UInt8} {cells : List (List UInt8)}
    (accepted : layout leading cells = .ok page) :
    let pointerEnd := leading.length + 8 + 2 * cells.length
    let contentStart := File.Write.pageSize - cells.flatten.length
    (Bytes.ofList page).slice? pointerEnd (some contentStart) =
      some (Bytes.replicate (contentStart - pointerEnd) 0) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Gap.layout_gap_slice accepted

end Silmaril.Formats.Sqlite.BTree.LeafWrite
