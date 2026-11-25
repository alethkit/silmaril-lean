module

public import Silmaril.Formats.Sqlite.File.Header.Frame.Thms
public import Silmaril.Formats.Sqlite.TableLeaf.Defs

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.TableLeaf.Open

private theorem open?_descriptor_frame (left right : Bytes)
    (descriptor : (File.parse? left).map (fun image => (image.header, image.pageCount, image.physicalPageCount)) =
      (File.parse? right).map (fun image => (image.header, image.pageCount, image.physicalPageCount)))
    (catalogue : ((File.parse? left).bind fun image => (image.page? 1).bind fun view => TableLeaf.read? view 100) =
      ((File.parse? right).bind fun image => (image.page? 1).bind fun view => TableLeaf.read? view 100))
    (table : ((File.parse? left).bind fun image => (image.page? 2).bind fun view => TableLeaf.read? view 0) =
      ((File.parse? right).bind fun image => (image.page? 2).bind fun view => TableLeaf.read? view 0)) :
    TableLeaf.open? left = TableLeaf.open? right := by
  cases leftParsed : File.parse? left with
  | none =>
    cases rightParsed : File.parse? right with
    | none => simp [TableLeaf.open?, leftParsed, rightParsed]
    | some image => simp [leftParsed, rightParsed] at descriptor
  | some li =>
    cases rightParsed : File.parse? right with
    | none => simp [leftParsed, rightParsed] at descriptor
    | some ri =>
      simp only [leftParsed, rightParsed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at descriptor
      obtain ⟨headers, pageCounts, physicalCounts⟩ := descriptor
      simp only [leftParsed, rightParsed, Option.bind_some] at catalogue table
      simp [TableLeaf.open?, leftParsed, rightParsed, headers, pageCounts, physicalCounts]
      simp only [← Option.bind_assoc, catalogue, table]

theorem open?_frame (left right : Bytes) (length : left.length = right.length)
    (same : ∀ i, i < 100 → (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i)
    (catalogue : ((File.parse? left).bind fun image => (image.page? 1).bind fun view => TableLeaf.read? view 100) =
      ((File.parse? right).bind fun image => (image.page? 1).bind fun view => TableLeaf.read? view 100))
    (table : ((File.parse? left).bind fun image => (image.page? 2).bind fun view => TableLeaf.read? view 0) =
      ((File.parse? right).bind fun image => (image.page? 2).bind fun view => TableLeaf.read? view 0)) :
    TableLeaf.open? left = TableLeaf.open? right :=
  open?_descriptor_frame left right (File.parse?_descriptor_frame left right length same) catalogue table

end Silmaril.Proofs.Formats.Sqlite.TableLeaf.Open
