module
import Silmaril.Formats.Sqlite.VirtualTable.Backed.Thms
meta import Silmaril.Formats.Sqlite.VirtualTable.Defs
meta import Silmaril.Formats.Sqlite.VirtualTable.Lifecycle
meta import Silmaril.Formats.Sqlite.VirtualTable.Backed.Defs

open Silmaril.Formats.Sqlite.VirtualTable

def fixture : Snapshot 1 :=
  ⟨[⟨Int64.maxValue, #v[3]⟩, ⟨2, #v[7]⟩, ⟨-5, #v[-8]⟩,
    ⟨0, #v[7]⟩, ⟨9, #v[9]⟩, ⟨Int64.minValue, #v[0]⟩], by decide⟩

def proposedQuery := Backed.query .desc 0 8
def rawScan : Relation 1 := [⟨Int64.maxValue, #v[3]⟩, ⟨9, #v[9]⟩, ⟨2, #v[7]⟩, ⟨0, #v[7]⟩]

def wrongOmit : Plan :=
  { Backed.plan .desc with arguments := [⟨1, true⟩, ⟨0, true⟩] }

-- These proposals pass the structural check and fail on the actual rows.
example : wrongOmit.validLayout proposedQuery.input = true := by decide
example : checkHonesty proposedQuery wrongOmit fixture rawScan = false := by decide
example : checkHonesty proposedQuery (Backed.plan .desc) fixture rawScan.reverse = false := by decide
example : checkHonesty proposedQuery (Backed.plan .desc) fixture (rawScan.drop 1) = false := by decide

example : checkHonesty proposedQuery
    { Backed.plan .desc with orderByConsumed := false } fixture rawScan.reverse = true := by decide

example : ¬ Honest proposedQuery wrongOmit fixture rawScan := by
  intro honest
  have checked := checkHonesty_iff.mpr honest
  have rejected : checkHonesty proposedQuery wrongOmit fixture rawScan = false := by decide
  simp [rejected] at checked

-- Sender order is the slot order, even when it differs from constraint-array order.
example : proposedQuery.argv (Backed.plan .desc) = .ok [8, 0] := rfl

def unusable : BestIndexInput 1 :=
  ⟨[⟨.rowid, .ge, false⟩, ⟨.value 0, .lt, true⟩], some .desc⟩

example : (Backed.plan .desc).validLayout unusable = false := by decide
example : (Backed.table fixture).xBestIndex unusable = .error .noPlan := rfl
example : Plan.validLayout
    { Backed.plan .desc with arguments := [⟨0, false⟩, ⟨0, false⟩] } proposedQuery.input = false :=
  by decide
example : Plan.validLayout { Backed.plan .desc with arguments := [⟨2, false⟩] }
    proposedQuery.input = false := by decide

def dishonestTable : Table 1 :=
  ⟨{ Backed.implementation with bestIndex := fun _ => .ok wrongOmit }, fixture⟩

def status {α : Type} : Except Error α → Option Error
  | .ok _ => none
  | .error error => some error

def lifecycle : Except Error (List (Option Error) × Bool) := do
  let conn ← (Connection.register Backed.implementation).xConnect fixture
  let (conn, first) ← conn.xOpen
  let (conn, second) ← conn.xOpen
  let before := status (conn.xRowid first)
  let (conn, failed) := conn.xFilter first (Backed.key .desc) [8]
  let failedRead := status (conn.xRowid first)
  let (conn, reset) := conn.xFilter first (Backed.key .desc) [8, Int64.maxValue]
  reset
  let head ← conn.xRowid first
  let badColumn := status (conn.xColumn first 1)
  let secondStillUnfiltered := status (conn.xNext second)
  let busy := status conn.xDisconnect
  let conn ← conn.xNext first
  let eof ← conn.xEof first
  let endRead := status (conn.xColumn first 0)
  let conn ← conn.xClose first
  let retired := status (conn.xRowid first)
  let conn ← conn.xClose second
  let conn ← conn.xDisconnect
  let conn ← conn.xConnect fixture
  let (conn, third) ← conn.xOpen
  let conn ← conn.xClose third
  let _ ← conn.close
  return ([before, status failed, failedRead, badColumn, secondStillUnfiltered, busy, endRead, retired],
    eof && head == Int64.maxValue && first < second && second < third)

def visit (fuel : Nat) (cursor : Cursor 1) : Except Error (List (Int64 × Int64)) := do
  if cursor.xEof then return []
  match fuel with
  | 0 => throw .atEnd
  | n + 1 =>
    let id ← cursor.xRowid
    let value ← cursor.xColumn 0
    return (id, value) :: (← visit n (← cursor.xNext))

def runCase (dir : Direction) (lo hi : Int64) : Except Error (List (Int64 × Int64) × Relation 1) := do
  let table := Backed.table fixture
  let query := Backed.query dir lo hi
  let (_, cursor) ← table.startQuery query
  let rows ← table.run query
  let audited ← table.runChecked query
  if rows != audited then throw .dishonestPlan
  return (← visit fixture.rows.length cursor, rows)

public def main : IO Unit := do
  unless status (dishonestTable.runChecked proposedQuery) == some .dishonestPlan do
    throw (IO.userError "audit accepted a false omit claim")
  let .ok (errors, ok) := lifecycle | throw (IO.userError "cursor lifecycle failed")
  unless ok && errors ==
      [some .unfiltered, some .argumentCount, some .argumentCount, some .columnOutOfRange,
        some .unfiltered, some .cursorsOpen, some .atEnd, some .unknownCursor] do
    throw (IO.userError s!"unexpected cursor transitions {repr errors}")
  for dir in [Direction.asc, Direction.desc] do
    for lo in [Int64.minValue, -5, -4, 0, 3, Int64.maxValue] do
      for hi in [-8, -7, 0, 7, 8, Int64.maxValue] do
        let .ok (scan, rows) := runCase dir lo hi
          | throw (IO.userError "Lean virtual-table query failed")
        IO.println s!"case {if dir == .asc then 1 else 2} {lo.toInt} {hi.toInt}"
        for (id, value) in scan do
          IO.println s!"scan {id.toInt} {value.toInt}"
        for row in rows do
          IO.println s!"row {row.rowid.toInt} {row.values[0].toInt}"
