module

import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.Shell.Defs

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile

private def rows (snapshot : Snapshot) : List String → Except String Snapshot
  | [] => .ok snapshot
  | idText :: amountText :: tail => do
    let some id := Shell.signed64? idText | throw "rowid must be a signed 64-bit integer"
    let some amount := Shell.signed64? amountText | throw "amount must be a signed 64-bit integer"
    let next ← (snapshot.insert id amount).mapError reprStr
    rows next.snapshot tail
  | [_] => .error "expected ROWID AMOUNT pairs"

public def main (args : List String) : IO Unit := do
  let path :: values := args
    | throw (IO.userError "usage: sqlite_image_lean OUTPUT [ROWID AMOUNT ...]")
  let snapshot ← IO.ofExcept (rows .empty values)
  let bytes ← IO.ofExcept ((Image.Checked.encode snapshot).mapError reprStr)
  IO.FS.withFile (System.FilePath.mk path) .writeNew fun handle => do
    handle.write bytes.data
    handle.flush
