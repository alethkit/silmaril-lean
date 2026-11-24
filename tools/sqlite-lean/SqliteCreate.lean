module

import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.Shell.Defs

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile

namespace SqliteCli

private def rows (snapshot : Snapshot) : List String → Except String Snapshot
  | [] => .ok snapshot
  | idText :: amountText :: tail => do
    let some id := Shell.signed64? idText | throw "rowid must be a signed 64-bit integer"
    let some amount := Shell.signed64? amountText | throw "amount must be a signed 64-bit integer"
    let next ← (snapshot.insert id amount).mapError reprStr
    rows next.snapshot tail
  | [_] => .error "expected ROWID AMOUNT pairs"

/-- Prepare and check the whole image before opening the destination exclusively. -/
public def create (path : System.FilePath) (values : List String) : IO Unit := do
  let snapshot ← IO.ofExcept (rows .empty values)
  let bytes ← IO.ofExcept ((Image.Checked.encode snapshot).mapError reprStr)
  IO.FS.withFile path .writeNew fun handle => do
    handle.write bytes.data
    handle.flush

end SqliteCli
