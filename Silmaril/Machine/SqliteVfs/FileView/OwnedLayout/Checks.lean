module

import Silmaril.Machine.SqliteVfs.FileView.OwnedLayout.Thms

namespace Silmaril.Machine.SqliteVfs.FileView.OwnedLayout

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.BTree
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

section Fixture

set_option maxRecDepth 4096

private def cell : List UInt8 :=
  LeafWrite.Cell.bytes ⟨7, Record.Write.amount (-129)⟩
private def serialized : List UInt8 :=
  (LeafWrite.layout [] [cell]).toOption.get (by decide)
private def beforePage : List UInt8 := List.replicate 512 0
private def file : FileState := ⟨beforePage ++ serialized, some .readOnly, 0⟩
private def cache : Cache := fun _ => some .vacant
private def page : Page := ⟨⟨0⟩, 2, 512⟩

example :
    let outcome := fill (readOnly 2048) file cache 0 page
    outcome.result = .ok serialized ∧
      outcome.trace = [⟨.read ⟨0⟩ 512 512, .ok serialized⟩] ∧
      ∃ part : File.View, (TableLeaf.cell? (File.View.ofBytes part.materialize) 0).bind TableLeaf.row? =
        some (7, [.integer 7, .integer (-129)]) := by
  obtain ⟨filled, _, part, _, _, row⟩ :=
    filled_layout_selected_row 2048 file cache 0 page
      (leading := []) (serialized := serialized) (cells := [cell])
      (beforePage := beforePage) (afterPage := [])
      0 7 (by decide) (-129) rfl rfl rfl rfl (by decide) (by decide) rfl rfl
  exact ⟨congrArg Outcome.result filled, congrArg Outcome.trace filled, part, row⟩

end Fixture

#print axioms filled_layout_selected_row

end Silmaril.Machine.SqliteVfs.FileView.OwnedLayout
