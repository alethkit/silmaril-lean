module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.TableLeaf.Open.Read

public section
namespace Silmaril.Formats.Sqlite.TableLeaf

/-- The ordinary table opener depends on the file header and length and the
two ordinary leaf reads. Matching those observations preserves its result. -/
theorem open?_frame (left right : Bytes) (length : left.length = right.length)
    (same : ∀ i, i < 100 → (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i)
    (catalogue : ((File.parse? left).bind fun image => (image.page? 1).bind fun view => TableLeaf.read? view 100) =
      ((File.parse? right).bind fun image => (image.page? 1).bind fun view => TableLeaf.read? view 100))
    (table : ((File.parse? left).bind fun image => (image.page? 2).bind fun view => TableLeaf.read? view 0) =
      ((File.parse? right).bind fun image => (image.page? 2).bind fun view => TableLeaf.read? view 0)) :
    TableLeaf.open? left = TableLeaf.open? right :=
  Silmaril.Proofs.Formats.Sqlite.TableLeaf.Open.open?_frame left right length same catalogue table

end Silmaril.Formats.Sqlite.TableLeaf
