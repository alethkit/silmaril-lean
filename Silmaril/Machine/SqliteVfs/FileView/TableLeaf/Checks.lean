module

import Silmaril.Machine.SqliteVfs.FileView.TableLeaf.Thms
meta import Silmaril.Formats.Sqlite.TableLeaf.Defs
meta import Silmaril.Formats.Sqlite.File.Defs
meta import Silmaril.Formats.Sqlite.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.TableLeaf

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.File (View)
-- A packed leaf with one local record, rowid 7 and an integer value 5.
private def leafBytes : Array UInt8 :=
  #[13, 0, 0, 0, 1, 1, 250, 0, 1, 250] ++ Array.replicate 496 0 ++ #[4, 7, 3, 0, 1, 5]

private def pageView (source : Silmaril.Formats.Bytes) (fits : 2 + 512 ≤ source.length) : View :=
  ⟨source, 2, 512, fits⟩

private def validSource : Silmaril.Formats.Bytes := ⟨⟨#[255, 255] ++ leafBytes⟩⟩
private def badSource : Silmaril.Formats.Bytes := ⟨⟨#[255, 255] ++ leafBytes.set! 0 10⟩⟩
private def validView : View := pageView validSource (by
  simp only [validSource, Silmaril.Formats.Bytes.length, ← ByteArray.size_data,
    leafBytes, Array.size_append, Array.size_replicate]
  decide)
private def badView : View := pageView badSource (by
  simp only [badSource, Silmaril.Formats.Bytes.length, ← ByteArray.size_data,
    leafBytes, Array.size_append, Array.size_replicate, Array.size_set!]
  decide)

private def rows (view : View) : Option (List (Int × List Value)) := do
  (← TableLeaf.read? view 0).mapM TableLeaf.row?

-- Runtime fixture checks are separate from the kernel-checked theorems.
#guard decide (rows validView = some [(7, [.integer 7, .integer 5])])
#guard decide (rows (View.ofBytes validView.materialize) = some [(7, [.integer 7, .integer 5])])
#guard (TableLeaf.read? badView 0).isNone
#guard (TableLeaf.read? (View.ofBytes badView.materialize) 0).isNone

#print axioms read_materialized
#print axioms image_page_fill_decode

end Silmaril.Machine.SqliteVfs.FileView.TableLeaf
