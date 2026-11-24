module

import Silmaril.Formats.Sqlite.WriteProfile.Thms

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private structure Trial where
  command : Command
  sql : String
  result : Except Error Success

private def smallest : Int64 := -9223372036854775808
private def largest : Int64 := 9223372036854775807

private def trials : List Trial := [
  ⟨.edit (.insert (.integer 3) (.integer 20)), "INSERT INTO sample VALUES (3,20);", .ok (.changed 1)⟩,
  ⟨.edit (.insert (.integer smallest) (.integer (-7))),
    "INSERT INTO sample VALUES (-9223372036854775808,-7);", .ok (.changed 1)⟩,
  ⟨.begin, "BEGIN;", .ok .transaction⟩,
  ⟨.edit (.update (.integer smallest) (.integer 8)),
    "UPDATE sample SET amount=8 WHERE id=-9223372036854775808;", .ok (.changed 1)⟩,
  ⟨.edit (.insert (.integer 1) (.integer 50)), "INSERT INTO sample VALUES (1,50);", .ok (.changed 1)⟩,
  ⟨.edit (.insert (.integer 1) (.integer 51)), "INSERT INTO sample VALUES (1,51);", .error .duplicateRowid⟩,
  ⟨.edit (.update (.integer 3) .null), "UPDATE sample SET amount=NULL WHERE id=3;", .error .notNull⟩,
  ⟨.edit (.insert (.integer 2) .null), "INSERT INTO sample VALUES (2,NULL);", .error .notNull⟩,
  ⟨.edit (.update (.integer 99) .null), "UPDATE sample SET amount=NULL WHERE id=99;", .ok (.changed 0)⟩,
  ⟨.edit (.delete (.integer 3)), "DELETE FROM sample WHERE id=3;", .ok (.changed 1)⟩,
  ⟨.rollback, "ROLLBACK;", .ok .transaction⟩,
  ⟨.begin, "BEGIN;", .ok .transaction⟩,
  ⟨.edit (.update (.integer 3) (.integer 20)), "UPDATE sample SET amount=20 WHERE id=3;", .ok (.changed 1)⟩,
  ⟨.edit (.delete (.integer 3)), "DELETE FROM sample WHERE id=3;", .ok (.changed 1)⟩,
  ⟨.edit (.delete (.integer 3)), "DELETE FROM sample WHERE id=3;", .ok (.changed 0)⟩,
  ⟨.edit (.insert (.integer largest) (.integer 0)),
    "INSERT INTO sample VALUES (9223372036854775807,0);", .ok (.changed 1)⟩,
  ⟨.commit, "COMMIT;", .ok .transaction⟩
]

private def scan : Vdbe.Program :=
  #[.openRead 0 2 0, .rewind 0 6, .column 0 0 1, .column 0 1 2,
    .resultRow 1 2, .next 0 2, .halt 0]

private def vmRows (state : State) : IO String := do
  let fuel := 3 + 4 * state.visible.rows.length
  let .halted result := Vdbe.run state.readDatabase scan fuel Vdbe.State.initial
    | throw (IO.userError "VM scan did not halt")
  check "VM success status" (result.halted == some 0)
  let rows ← result.rows.mapM fun
    | [.integer id, .integer amount] => pure s!"{id.toInt}:{amount.toInt}"
    | _ => throw (IO.userError "VM row failed the read profile")
  pure (String.intercalate "," rows)

private def sameResult : Except Error Success → Except Error Success → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def countText (command : Command) (result : Except Error Success) : String :=
  match command, result with
  | .edit _, .ok (.changed n) => toString n
  | .edit _, _ => "0"
  | _, _ => "-"

private def observe (trial : Trial) : String :=
  let count := match trial.command with
    | .edit _ => "changes()"
    | _ => "'-'"
  "SELECT " ++ count ++ " || '|' || COALESCE((SELECT group_concat(id || ':' || amount, ',') " ++
    "FROM (SELECT id, amount FROM sample ORDER BY id)), '');"

private def expectedNativeErrors : List String := [
  "UNIQUE constraint failed: sample.id",
  "NOT NULL constraint failed: sample.amount",
  "NOT NULL constraint failed: sample.amount"
]

private def native (sqlite : String) (model : List String) : IO Unit := do
  let script := ".bail off\nCREATE TABLE sample(id INTEGER PRIMARY KEY, amount INTEGER NOT NULL) STRICT;\n" ++
    String.intercalate "\n" (trials.map fun trial => trial.sql ++ "\n" ++ observe trial) ++ "\n"
  let run ← IO.Process.output
    { cmd := sqlite, args := #["-init", "/dev/null", "-batch", "-list", "-noheader", ":memory:"] }
    (some script)
  let rows := (run.stdout.splitOn "\n").filter (! ·.isEmpty)
  let errors := (run.stderr.splitOn "\n").filter (! ·.isEmpty)
  check s!"native rows/counts disagree\nexpected {model}\ngot {rows}" (rows == model)
  check s!"unexpected native exit or diagnostics: {run.stderr}"
    (run.exitCode == 1 && errors.length == expectedNativeErrors.length &&
      (errors.zip expectedNativeErrors).all (fun (line, expected) => (line.splitOn expected).length == 2))
  let version ← IO.Process.run { cmd := sqlite, args := #["--version"] }
  IO.println s!"Native SQLite {version.trimAscii} agreed on {trials.length} ordered VM snapshots and change counts"

private def model : IO (List String) := do
  let mut state := State.empty
  let mut observations := []
  for trial in trials do
    let outcome := step state trial.command
    check s!"Lean result for {trial.sql}" (sameResult outcome.result trial.result)
    state := outcome.state
    observations := (countText trial.command outcome.result ++ "|" ++ (← vmRows state)) :: observations
  check "committed rowid order and signed limits" ((← vmRows state) == "-9223372036854775808:-7,9223372036854775807:0")
  let pending := (step state .begin).state
  let rejects : List (State × Command × Error) := [
    (pending, .begin, .transactionActive),
    (state, .rollback, .noTransaction),
    (state, .commit, .noTransaction),
    (state, .edit (.insert .null (.integer 1)), .rowidType),
    (pending, .edit (.update (.integer largest) (.text "42")), .amountType)
  ]
  for (before, command, error) in rejects do
    let result := step before command
    check "explicit profile or transaction rejection" (sameResult result.result (.error error))
    check "rejection preserves committed and visible rows"
      ((← vmRows result.state) == (← vmRows before) &&
       (← vmRows ⟨result.state.committed, none⟩) == (← vmRows ⟨before.committed, none⟩) &&
       result.state.pending.isSome == before.pending.isSome)
  pure observations.reverse

public def main (args : List String) : IO Unit := do
  let observations ← model
  match args with
  | [] => pure ()
  | ["--sqlite3", sqlite] => native sqlite observations
  | _ => throw (IO.userError "usage: sqlite_write_profile_tests [--sqlite3 PATH]")
  IO.println "SQLite write profile: VM scans, counts, rejection, statement atomicity, commit and rollback passed"
