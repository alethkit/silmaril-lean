module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.TableLeaf.Subview.Read

public section
namespace Silmaril.Formats.Sqlite.TableLeaf

/-- A cell successfully read from the materialized bytes of an admitted
subview is also readable directly in the parent. The key and payload agree,
and the cell offsets in the parent include the subview's placement. -/
theorem cell?_materialized_shift (parent part : File.View) (base count offset : Nat)
    (sliced : parent.sub? base count = some part) (cell : Cell)
    (decoded : cell? (File.View.ofBytes part.materialize) offset = some cell) :
    cell? parent (base + offset) =
      some { cell with start := base + cell.start, stop := base + cell.stop } :=
  Silmaril.Proofs.Formats.Sqlite.TableLeaf.Subview.cell?_materialized_shift
    parent part base count offset sliced cell decoded

end Silmaril.Formats.Sqlite.TableLeaf
