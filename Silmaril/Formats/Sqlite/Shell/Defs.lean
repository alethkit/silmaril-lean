module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
public import Silmaril.Formats.Sqlite.Vdbe.Defs

@[expose] public section
namespace Silmaril.Formats.Sqlite.Shell

inductive Column where
  | id
  | amount

def Column.name : Column → String
  | .id => "id"
  | .amount => "amount"

structure Query where
  columns : List Column
  key : Option Int64 := none
  limit : Option Nat := none
  offset : Nat := 0
  descending : Bool := false

def signed64? (text : String) : Option Int64 := do
  let value ← text.toInt?
  if -(2^63 : Int) ≤ value ∧ value < 2^63 then some (Int64.ofInt value) else none

def selectColumns? : List String → Option (List Column)
  | ["*"] | ["id", ",", "amount"] => some [.id, .amount]
  | ["amount", ",", "id"] => some [.amount, .id]
  | ["id"] => some [.id]
  | ["amount"] => some [.amount]
  | _ => none

def parse? (sql : String) : Option Query := do
  let separated := ((sql.toLower.replace "," " , ").replace "=" " = ").replace ";" " ; "
  let words := ((separated.map fun c => if c.isWhitespace then ' ' else c).splitOn " ")
    |>.filter (! ·.isEmpty)
  let words := match words.reverse with
    | ";" :: rest => rest.reverse
    | _ => words
  let "select" :: terms ← pure words | none
  let (columns, after) := terms.span (· != "from")
  let "from" :: "sample" :: tail ← pure after | none
  let columns ← selectColumns? columns
  let (key, tail) ← match tail with
    | "where" :: "id" :: "=" :: value :: rest => do
      let key ← signed64? value
      pure (some key, rest)
    | _ => some (none, tail)
  let (descending, tail) := match tail with
    | "order" :: "by" :: "id" :: "desc" :: rest => (true, rest)
    | "order" :: "by" :: "id" :: "asc" :: rest => (false, rest)
    | "order" :: "by" :: "id" :: rest => (false, rest)
    | _ => (false, tail)
  match tail with
  | [] => some ⟨columns, key, none, 0, descending⟩
  | ["limit", count] => do
    let count ← count.toNat?
    pure ⟨columns, key, some count, 0, descending⟩
  | ["limit", count, "offset", offset] => do
    let count ← count.toNat?
    let offset ← offset.toNat?
    pure ⟨columns, key, some count, offset, descending⟩
  | _ => none

def scan : Vdbe.Program :=
  #[.openRead 0 2 0, .rewind 0 6, .column 0 0 1, .column 0 1 2,
    .resultRow 1 2, .next 0 2, .halt 0]

def seek (key : Int64) : Vdbe.Program :=
  #[.openRead 0 2 0, .int64 key 1, .seekRowid 0 6 1, .column 0 0 1, .column 0 1 2,
    .resultRow 1 2, .halt 0]

structure Result where
  columns : List String
  rows : List (List Int)

def execute (table : Vdbe.Table) (query : Query) : Except String Result := do
  let database : Vdbe.Database := fun db root =>
    if db == 0 && root == 2 then some table else none
  let program := query.key.map seek |>.getD scan
  let .halted final := Vdbe.run database program (7 + 4 * table.entries.length) .initial
    | throw "read-only VM did not halt"
  if final.halted != some 0 then throw "read-only VM returned an error"
  let ordered := if query.descending then final.rows.reverse else final.rows
  let rows := (ordered.drop query.offset).take (query.limit.getD ordered.length)
  let rows ← rows.mapM fun row =>
    match row with
    | [.integer id, .integer amount] =>
      pure (query.columns.map fun column => match column with
        | .id => id.toInt
        | .amount => amount.toInt)
    | _ => throw "unexpected VM row"
  return ⟨query.columns.map Column.name, rows⟩

end Silmaril.Formats.Sqlite.Shell
