module

import SqliteCreate

public def main (args : List String) : IO Unit := do
  let path :: values := args
    | throw (IO.userError "usage: sqlite_image_lean OUTPUT [ROWID AMOUNT ...]")
  SqliteCli.create (System.FilePath.mk path) values
