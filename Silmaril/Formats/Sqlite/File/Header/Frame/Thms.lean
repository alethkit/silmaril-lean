module

public import Silmaril.Formats.Sqlite.File.Defs
import Silmaril.Proofs.Formats.Sqlite.File.Header.Frame.Read

public section
namespace Silmaril.Formats.Sqlite.File

/-- The ordinary header parser depends only on its first 100 bytes after
the source passes the initial length guard. -/
theorem parseHeader?_frame (left right : Bytes)
    (leftFits : 100 ≤ left.length) (rightFits : 100 ≤ right.length)
    (same : ∀ i, i < 100 → (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i) :
    File.parseHeader? left = File.parseHeader? right :=
  Silmaril.Proofs.Formats.Sqlite.File.Header.Frame.parseHeader?_frame left right leftFits rightFits same

/-- Matching header bytes and total length preserve the ordinary parsed
header and both page counts, including failure to parse a descriptor. -/
theorem parse?_descriptor_frame (left right : Bytes)
    (length : left.length = right.length)
    (same : ∀ i, i < 100 → (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i) :
    (File.parse? left).map (fun image => (image.header, image.pageCount, image.physicalPageCount)) =
      (File.parse? right).map (fun image => (image.header, image.pageCount, image.physicalPageCount)) :=
  Silmaril.Proofs.Formats.Sqlite.File.Header.Frame.parse?_descriptor_frame left right length same

end Silmaril.Formats.Sqlite.File
