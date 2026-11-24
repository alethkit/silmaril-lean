module

public import Silmaril.Cli.Args.Defs

/-! The native Lean SQLite front end. SQL and file admission belong to the
driver. The portable process observation interface lives in `Cli.Behaviour`. -/
@[expose] public section
namespace Silmaril.Cli.Spec.LeanSqliteShell

def command : Command := Command.withHelp {
  name := "sqlite_lean"
  about := "Read an immutable SQLite sample database or create a fresh one."
  exits := [(0, "success"), (1, "SQL, database or I/O error"), (2, "usage error")]
  subs := [
    {
      name := "query"
      about := "Run one supported SELECT against an immutable snapshot."
      pos := [arg "database" .path .one "Clean immutable database",
        arg "sql" .str .optional "One SELECT, or omit to read UTF-8 stdin through EOF"] },
    {
      name := "schema"
      about := "Print the validated sample table's CREATE statement."
      pos := [arg "database" .path .one "Clean immutable database"] },
    {
      name := "create"
      about := "Exclusively create a fresh STRICT sample database."
      pos := [arg "output" .path .one "New database path",
        { arg "values" .str .many "Signed ROWID AMOUNT pairs (use -- before negative values)"
          with metavar := "VALUE" }] }]
}

/-- Existing spellings keep their original argument roles, including signed
arguments and paths beginning with a hyphen. -/
def normalize : List String → List String
  | ["--immutable", database, sql] => ["query", "--", database, sql]
  | "--create" :: output :: values => "create" :: "--" :: output :: values
  | args => args

inductive Request where
  | query (database : String) (sql : Option String)
  | schema (database : String)
  | create (output : String) (values : List String)

/-- Interpret the derived matches while keeping filesystem and SQL actions
out of the front end. A missing query argument denotes stdin. -/
def Request.ofMatches (matched : Matches) : Option Request :=
  match matched.path with
  | ["query"] => (matched.str? "database").map fun database => .query database (matched.str? "sql")
  | ["schema"] => (matched.str? "database").map .schema
  | ["create"] => (matched.str? "output").map fun output => .create output (matched.strs "values")
  | _ => none

end Silmaril.Cli.Spec.LeanSqliteShell
