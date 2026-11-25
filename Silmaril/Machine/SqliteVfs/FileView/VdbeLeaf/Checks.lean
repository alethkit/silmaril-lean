module

import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Thms
meta import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs
meta import Silmaril.Formats.Sqlite.TableLeaf.Defs
meta import Silmaril.Formats.Sqlite.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf

open Silmaril.Formats.Sqlite

-- Serial type 0 gives the rowid alias its required NULL placeholder.
-- Serial type 8 encodes integer zero with the same payload length.
private def source (aliasType : UInt8) : Silmaril.Formats.Bytes :=
  ⟨⟨#[255, 13, 0, 0, 0, 1, 1, 250, 0, 1, 250] ++
    Array.replicate 496 0 ++ #[4, 7, 3, aliasType, 1, 5]⟩⟩

private def view (aliasType : UInt8) : File.View :=
  ⟨source aliasType, 1, 512, by
    simp only [source, Silmaril.Formats.Bytes.length, ← ByteArray.size_data,
      Array.size_append, Array.size_replicate]
    exact Nat.le_refl _⟩

private def scan : Vdbe.Program :=
  #[.openRead 0 2 0, .rewind 0 6, .column 0 0 1, .column 0 1 2,
    .resultRow 1 2, .next 0 2, .halt 0]

private def emitsExpected (input : File.View) : Bool :=
  match run? input 0 0 2 scan 16 .initial with
  | some (.halted state) =>
      decide (state.rows = [[.integer 7, .integer 5]] ∧ state.halted = some 0)
  | _ => false

private def rejectsRow (input : File.View) : Bool :=
  match TableLeaf.read? input 0 with
  | some [cell] => (TableLeaf.row? cell).isNone ∧
      (run? input 0 0 2 scan 16 .initial).isNone
  | _ => false

-- These evaluator checks exercise the implementation and are outside theorem proof terms.
#guard emitsExpected (view 0)
#guard emitsExpected (File.View.ofBytes (view 0).materialize)
#guard rejectsRow (view 8)
#guard rejectsRow (File.View.ofBytes (view 8).materialize)

#print axioms run_rejected_leaf
#print axioms run_rejected_rows
#print axioms run_materialized
#print axioms image_page_fill_run

end Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf
