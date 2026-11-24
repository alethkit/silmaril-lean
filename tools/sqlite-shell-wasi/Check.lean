module

import Silmaril.Cli.Io.Run.Defs
import Silmaril.Cli.Spec.SqliteShell.Defs
meta import Silmaril.Cli.Io.Run.Defs
meta import Silmaril.Cli.Spec.SqliteShell.Defs

open Silmaril.Cli Silmaril.Cli.Io Silmaril.Cli.Spec.SqliteShell

private abbrev Runner := Case → IO Snap

private def expect (name : String) (ok : Bool) (detail : String) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}: {detail}")
  IO.println s!"PASS: {name}"

private def expectSnap (name : String) (actual expected : Snap) : IO Unit :=
  expect name (actual == expected) (s!"expected {showSnap expected}, got {showSnap actual}")

private def expectRows (name : String) (shell : Shell) (snap : Snap) (expected : Rows) :
    IO Unit :=
  match shell.rows expected.columns snap with
  | .ok actual => expect name (actual == expected) (reprStr actual)
  | .error err => throw (IO.userError s!"FAIL: {name}: {err}: {showSnap snap}")

private def output (stdout : String := "") (stderr : String := "") (exit : ExitCode := 0) :
    Snap :=
  { stdout := utf8 stdout, stderr := utf8 stderr, exit }

private def runChecks (wasmtime wasm sqlite libDir : String) (leanShell : Option String) :
    IO Unit := do
  let native : Runner := fun c =>
    runBinary sqlite [] { c with env := [("HOME", "."), ("LD_LIBRARY_PATH", libDir)] }
  let wasi (preopen : Bool) : Runner := fun c =>
    runBinary wasmtime (["run", "-C", "cache=n", "--argv0", "sqlite3", "--env", "HOME=."] ++
      (if preopen then ["--dir=."] else []) ++ [wasm]) c

  let version : Case := { name := "version", args := ["-version"] }
  let sourceId := "3.54.1 2026-10-16 14:45:20 " ++
    "555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76"
  expectSnap "native version" (← native version) (output (sourceId ++ " (64-bit)\n"))
  expectSnap "WASI version" (← wasi false version) (output (sourceId ++ " (32-bit)\n"))

  let shared : List (Case × Snap) := [
    ({ name := "argv with spaces and UTF-8",
       args := ["-batch", "-noheader", "-list", ":memory:", "SELECT 'one argument', 'héllo', 6*7;"] },
      output "one argument|héllo|42\n"),
    ({ name := "stdin SQL and dot command", args := ["-batch", ":memory:"],
       stdin := utf8 ".mode list\nSELECT 4;\n.exit 7\nSELECT 5;\n" },
      output "4\n" "" 7),
    ({ name := "stdin syntax error with -bail", args := ["-batch", "-bail", ":memory:"],
       stdin := utf8 "SELECT 4;\nSELECT FROM;\nSELECT 5;\n" },
      output "4\n" "Parse error near line 2: near \"FROM\": syntax error\n  SELECT FROM;\n         ^--- error here\n" 1),
    ({ name := "missing table in argv", args := ["-batch", ":memory:", "SELECT * FROM missing;"] },
      output "" "Parse error in 3rd command line argument: no such table: missing\n" 1)]
  for (c, expected) in shared do
    expectSnap s!"native {c.name}" (← native c) expected
    expectSnap s!"WASI {c.name}" (← wasi false c) expected

  let badOption : Case := { name := "unknown option", args := ["-batch", "-xyz"] }
  let optionError := ": Error: unknown option: -xyz\nUse -help for a list of options.\n"
  expectSnap "native argv[0] in diagnostic" (← native badOption) (output "" (sqlite ++ optionError) 1)
  expectSnap "WASI argv[0] in diagnostic" (← wasi false badOption) (output "" ("sqlite3" ++ optionError) 1)

  let disabled : List (String × String) := [
    ("shell", "Usage: .system COMMAND\n"),
    ("load", "Usage: .load FILE ?ENTRYPOINT?\n")]
  for (command, diagnostic) in disabled do
    let c : Case := { name := command, args := ["-batch", ":memory:", "." ++ command] }
    expectSnap s!"native .{command}" (← native c) (output "" diagnostic 1)
    expectSnap s!"WASI .{command}" (← wasi false c)
      (output "" s!"Error: unknown command or invalid arguments:  \"{command}\". Enter \".help\" for help\n" 1)

  let database := "sample.sqlite"
  let create : Case := { name := "create sample", args := ["-batch", database,
    "PRAGMA page_size=512; CREATE TABLE sample(id INTEGER PRIMARY KEY, amount INTEGER NOT NULL) STRICT; " ++
    "INSERT INTO sample VALUES(5,-10),(-9223372036854775808,7),(9223372036854775807,0),(1,9);"] }
  let created ← wasi true create
  let [(path, bytes)] := created.files
    | throw (IO.userError s!"expected one database after WASI create, got {showSnap created}")
  expect "WASI preopen creates a 1024-byte SQLite database"
    (created.exit == 0 && created.stdout.isEmpty && created.stderr.isEmpty &&
      path == [database] && bytes.length == 1024 && bytes.take 16 == utf8 "SQLite format 3\x00")
    (showSnap created)
  let fixture := [(database, bytes)]
  let cases : List (String × String × Rows) := [
    ("ordered scan", "SELECT * FROM sample ORDER BY id;",
      ⟨["id", "amount"], [[-9223372036854775808, 7], [1, 9], [5, -10], [9223372036854775807, 0]]⟩),
    ("projection and slicing", "SELECT amount,id FROM sample ORDER BY id LIMIT 2 OFFSET 1;",
      ⟨["amount", "id"], [[9, 1], [-10, 5]]⟩),
    ("point lookup", "SELECT amount FROM sample WHERE id=-9223372036854775808;",
      ⟨["amount"], [[7]]⟩),
    ("empty point lookup", "SELECT id FROM sample WHERE id=4;", ⟨["id"], []⟩)]
  for (name, sql, expected) in cases do
    let upstream : Case := { name, args := Shell.upstream.args database sql, files := fixture }
    let snap ← wasi true upstream
    expectSnap s!"WASI/native raw {name}" snap (← native upstream)
    expectRows s!"WASI/native typed {name}" .upstream snap expected
    if let some exe := leanShell then
      let snap ← runBinary exe [] { name, args := Shell.lean.args database sql, files := fixture }
      expectRows s!"Lean typed {name}" .lean snap expected

  let read : Case := {
    name := "no preopen"
    args := Shell.upstream.args database "SELECT id FROM sample;"
    files := fixture
  }
  expectSnap "WASI cannot open a host file without a preopen" (← wasi false read)
    (output "" "Error: unable to open database \"sample.sqlite\": unable to open database file\n" 1)

  let sql := "DELETE FROM sample;"
  let readOnly : Case := {
    name := "read-only write refusal"
    args := Shell.upstream.args database sql
    files := fixture
  }
  let refusal := output "" "Error in 5th command line argument: attempt to write a readonly database\n" 1
  expectSnap "native refuses write with -readonly" (← native readOnly) refusal
  expectSnap "WASI refuses write with -readonly" (← wasi true readOnly) refusal

  let aggregate := "SELECT count(*) AS n FROM sample;"
  let countRows : Case := {
    name := "aggregate"
    args := Shell.upstream.args database aggregate
    files := fixture
  }
  let countResult := output "[{\"n\":4}]\n"
  expectSnap "native accepts aggregate" (← native countRows) countResult
  expectSnap "WASI accepts aggregate" (← wasi true countRows) countResult
  if let some exe := leanShell then
    let unsupported := output "" "uncaught exception: unsupported SELECT\n" 1
    for (name, query) in [("aggregate", aggregate), ("write", sql)] do
      let snap ← runBinary exe [] { name, args := Shell.lean.args database query, files := fixture }
      expectSnap s!"Lean refuses {name} at SQL profile boundary" snap unsupported
  else
    IO.println "SKIP: Lean executable comparison (pass SQLITE_LEAN_EXE to check.sh)"

public def main : List String → IO UInt32
  | wasmtime :: wasm :: sqlite :: libDir :: rest => do
    runChecks wasmtime wasm sqlite libDir rest.head?
    return 0
  | _ => do
    IO.eprintln "usage: Check.lean WASMTIME WASM NATIVE_SQLITE NATIVE_LIB_DIR [SQLITE_LEAN_EXE]"
    return 2
