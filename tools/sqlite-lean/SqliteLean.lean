module

import Lean.Data.Json
import Silmaril.Formats.Sqlite.Shell.Defs
import SqliteCreate

open Silmaril.Formats.Sqlite

private def rejectSidecars (path : System.FilePath) : IO Unit := do
  for suffix in ["-journal", "-wal", "-shm"] do
    if ← (System.FilePath.mk (path.toString ++ suffix)).pathExists then
      throw (IO.userError "SQLite sidecar present; expected a clean immutable snapshot")

private def snapshot (path : System.FilePath) : IO Silmaril.Formats.Bytes := do
  let canonical ← IO.FS.realPath path
  rejectSidecars path
  rejectSidecars canonical
  let metadata ← canonical.metadata
  unless metadata.type == .file && metadata.byteSize == 1024 do
    throw (IO.userError "expected a regular 1024-byte snapshot")
  let bytes ← IO.FS.withFile canonical .read fun file => file.read 1025
  rejectSidecars path
  rejectSidecars canonical
  unless bytes.size == 1024 do throw (IO.userError "snapshot size changed")
  pure ⟨bytes⟩

private def select (path : System.FilePath) (sql : String) : IO Unit := do
  let some query := Shell.parse? sql | throw (IO.userError "unsupported SELECT")
  let bytes ← snapshot path
  let some table := TableLeaf.open? bytes | throw (IO.userError "malformed or unsupported SQLite image")
  let result ← IO.ofExcept (Shell.execute table query)
  IO.println (Lean.Json.mkObj [
    ("columns", Lean.toJson result.columns), ("rows", Lean.toJson result.rows)]).compress

public def main : List String → IO Unit
  | ["--immutable", path, sql] => select (System.FilePath.mk path) sql
  | "--create" :: path :: values => SqliteCli.create (System.FilePath.mk path) values
  | _ => throw (IO.userError ("usage: sqlite_lean --immutable DATABASE SELECT\n" ++
      "       sqlite_lean --create OUTPUT [ROWID AMOUNT ...]"))
