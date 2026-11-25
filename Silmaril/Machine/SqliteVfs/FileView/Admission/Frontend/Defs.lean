module

public import Silmaril.Formats.Sqlite.Shell.Defs
public import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend

open Silmaril.Formats.Sqlite

inductive QueryError where
  | unsupportedSql
  | unreadableLeaf
  | execution (message : String)

/-- Execute the parsed frontend query on its logical table, preserving its
execution error text. -/
def executeQuery (table : Vdbe.Table) (parsed : Shell.Query) : Except QueryError Shell.Result :=
  (Shell.execute table parsed).mapError .execution

/-- Run the published restricted frontend against a supplied leaf. -/
def query (view : File.View) (base : Nat) (sql : String) : Except QueryError Shell.Result := do
  let some parsed := Shell.parse? sql | .error .unsupportedSql
  let some table := FileView.VdbeLeaf.table? view base | .error .unreadableLeaf
  executeQuery table parsed

end Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend
