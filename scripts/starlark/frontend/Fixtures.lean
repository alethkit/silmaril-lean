module

import Lean.Data.Json
import Silmaril.Languages.Starlark.Frontend.Checks
meta import Silmaril.Languages.Starlark.Frontend.Checks
import Silmaril.Languages.Starlark.Frontend.Module.Checks
meta import Silmaril.Languages.Starlark.Frontend.Module.Checks

open Lean Silmaril.Languages.Starlark.Frontend
open Silmaril.Languages.Starlark.Frontend.Module (Observation controls)

private def moduleObservation (expected : Observation) : Json :=
  let (phase, want) := match expected with
    | .exportedInt value => ("publication", toString value)
    | .undefinedName name => ("validation", s!"undefined: {name}")
    | .missingArgument name => ("runtime", s!"missing 1 argument ({name})")
  Json.mkObj [("phase", toJson phase), ("want", toJson want)]

public def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one fixture output path")
  let entries := fixtures.toArray.map fun fixture => Json.mkObj
    [("name", toJson fixture.name), ("source", toJson fixture.source),
     ("accepts", toJson fixture.goAccepts)]
  let modules := controls.toArray.map fun control =>
    Json.mkObj [("name", toJson control.name), ("source", toJson control.source),
      ("accepts", toJson true), ("module", moduleObservation control.expected)]
  IO.FS.writeFile output (Json.arr (entries ++ modules)).compress
