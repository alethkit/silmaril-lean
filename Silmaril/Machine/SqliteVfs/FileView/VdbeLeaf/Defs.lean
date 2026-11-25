module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
public import Silmaril.Formats.Sqlite.Vdbe.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf

open Silmaril.Formats.Sqlite

/-- Build one keyed table from the packed leaf after every record is accepted
by the landed row decoder. -/
def table? (view : File.View) (base : Nat) : Option Vdbe.Table := do
  let cells ← TableLeaf.read? view base
  let rows ← cells.mapM TableLeaf.row?
  pure (BTree.Query.ReadModel.ofList rows)

/-- Expose one decoded table at a caller-designated database and root. -/
def database (table : Vdbe.Table) (db root : Nat) : Vdbe.Database :=
  fun otherDb otherRoot => if otherDb = db ∧ otherRoot = root then some table else none

/-- Run only after the leaf and all its rows decode. An absent result is
a decode rejection. A present result retains the VDBE outcome and state. -/
def run? (view : File.View) (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) : Option Vdbe.RunResult := do
  let table ← table? view base
  pure (Vdbe.run (database table db root) program fuel initial)

end Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf
