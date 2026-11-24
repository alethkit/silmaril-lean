module

public import Lean.Data.Json
public import Silmaril.Cli.Io.Check.Defs

/-!
# CLI observations of a read-only SQLite snapshot

This adapter compares selected integer SELECTs on the portable Lean shell's
`sample(id, amount)` snapshot profile. The caller supplies the SQL and ordered,
distinct result column names. It projects successful process snapshots to typed
rows. For empty upstream results the column list comes from the invocation.
The observed exit status, raw diagnostics and changed files remain available in
`Io.Snap`. The adapter leaves SQL acceptance and file validation to each shell.
-/

public section

namespace Silmaril.Cli.Spec.SqliteShell

/-- The upstream C shell (native or WASI) and the portable Lean shell. -/
inductive Shell where
  | upstream
  | lean
deriving Repr, DecidableEq

/-- Arguments after `argv[0]` for one read-only query. Run upstream in a fresh
directory with `HOME=.` and no `.sqliterc`. The Lean shell expects a stable
1024-byte snapshot and refuses active sidecars. -/
def Shell.args (shell : Shell) (database sql : String) : List String :=
  match shell with
  | .upstream => ["-batch", "-readonly", "-json", database, sql]
  | .lean => ["--immutable", database, sql]

/-- The common view of a successful query. -/
structure Rows where
  columns : List String
  rows : List (List Int)
deriving Repr, DecidableEq

private def upstreamRows (columns : List String) (raw : Lean.Json) :
    Except String (List (List Int)) := do
  let rows ← raw.getArr?
  rows.toList.mapM fun row => do
    let obj ← row.getObj?
    unless obj.size == columns.length do throw "unexpected upstream columns"
    columns.mapM (row.getObjValAs? Int)

/-- Decode a clean, successful snapshot. Preserve integer precision across the
JSON carriers. Upstream emits row objects and no bytes for an empty result.
Lean emits an object with explicit columns and positional integer rows. -/
def Shell.rows (shell : Shell) (columns : List String) (snap : Io.Snap) :
    Except String Rows := do
  unless snap.exit == 0 && snap.stderr.isEmpty && snap.files.isEmpty do
    throw "expected success, empty stderr and no new or changed files"
  let some text := String.fromUTF8? ⟨snap.stdout.toArray⟩
    | throw "stdout is not UTF-8"
  let rows ← match shell with
    | .upstream =>
      if text.isEmpty then .ok [] else upstreamRows columns (← Lean.Json.parse text)
    | .lean => do
      let raw ← Lean.Json.parse text
      let actual ← raw.getObjValAs? (List String) "columns"
      unless actual == columns do throw "unexpected Lean columns"
      let rows ← raw.getObjValAs? (List (List Int)) "rows"
      unless rows.all (fun row => row.length == columns.length) do
        throw "unexpected Lean row width"
      .ok rows
  return ⟨columns, rows⟩

end Silmaril.Cli.Spec.SqliteShell

end
