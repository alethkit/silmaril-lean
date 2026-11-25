module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.TableLeaf.Cell

public section
namespace Silmaril.Formats.Sqlite.TableLeaf

/-- An accepted leaf cell is unchanged in a second view that contains its full
physical extent and agrees on `[start, cell.stop)` at view-relative offsets.
The result includes the signed rowid, copied payload, and original offsets. -/
theorem cell?_frame (left right : File.View) (start : Nat) (cell : Cell)
    (parsed : cell? left start = some cell) (fits : cell.stop ≤ right.length)
    (same : ∀ i, start ≤ i → i < cell.stop → left.get? i = right.get? i) :
    cell? right start = some cell :=
  Silmaril.Proofs.Formats.Sqlite.TableLeaf.cell?_frame left right start cell parsed fits same

end Silmaril.Formats.Sqlite.TableLeaf
