module

import Lean.Data.Json
import Silmaril.Cli.Spec.LeanSqliteShell.Defs
import Silmaril.Formats.Sqlite.Shell.Defs
import SqliteCreate

open Silmaril.Formats.Sqlite
open Silmaril.Cli.Spec.LeanSqliteShell

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

private def openTable (path : System.FilePath) : IO Vdbe.Table := do
  let bytes ← snapshot path
  let some table := TableLeaf.open? bytes | throw (IO.userError "malformed or unsupported SQLite image")
  pure table

private def select (path : System.FilePath) (sql : String) : IO Unit := do
  let some query := Shell.parse? sql | throw (IO.userError "unsupported SELECT")
  let table ← openTable path
  let result ← IO.ofExcept (Shell.execute table query)
  IO.println (Lean.Json.mkObj [
    ("columns", Lean.toJson result.columns), ("rows", Lean.toJson result.rows)]).compress

private def runRequest : Request → IO Unit
  | .query database sql => do
    let sql ← match sql with
      | some text => pure text
      | none => (← IO.getStdin).readToEnd
    select (System.FilePath.mk database) sql
  | .schema database => do
    let _ ← openTable (System.FilePath.mk database)
    IO.println (IntTable.schemaSql ++ ";")
  | .create path values => SqliteCli.create (System.FilePath.mk path) values

private def run (matched : Silmaril.Cli.Matches) : IO UInt32 := do
  let some request := Request.ofMatches matched | do
    IO.eprintln "sqlite_lean: invalid command arguments"
    return 2
  runRequest request
  return 0

private def runReported (matched : Silmaril.Cli.Matches) : IO UInt32 := do
  try run matched
  catch error =>
    IO.eprintln s!"sqlite_lean: {error}"
    return 1

public def main (args : List String) : IO UInt32 :=
  let normalized := normalize args
  -- Legacy requests retain the Lean runtime's exception diagnostics.
  command.main (if normalized == args then runReported else run) normalized
