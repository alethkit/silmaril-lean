module

import Lean.Data.Json
import Silmaril.Languages.Starlark.Frontend.Checks
meta import Silmaril.Languages.Starlark.Frontend.Checks

open Lean Silmaril.Languages.Starlark.Frontend

public def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one fixture output path")
  let entries := fixtures.toArray.map fun fixture => Json.mkObj
    [("name", toJson fixture.name), ("source", toJson fixture.source),
     ("accepts", toJson fixture.goAccepts)]
  IO.FS.writeFile output (Json.arr entries).compress
