module

public meta import Silmaril.Wasm.Binary.Core.Decode
public meta import Silmaril.Wasm.Validation.Check.Validate

meta section

open Silmaril.Wasm

private def elapsed (label : String) (start : Nat) : IO Unit := do
  let stop ← IO.monoNanosNow
  IO.println s!"{label}_ns={stop - start}"

public def main (args : List String) : IO UInt32 := do
  let [mode, input] := args | throw (IO.userError "usage: Benchmark.lean {parse|validate} INPUT.wasm")
  unless mode == "parse" || mode == "validate" do
    throw (IO.userError "expected parse or validate")
  let bytes ← IO.FS.readBinFile input
  let beforeParse ← IO.monoNanosNow
  let m ← match Binary.Core.Decode.decodeModule bytes with
    | .ok m => pure m
    | .error msg => throw (IO.userError s!"Core.decodeModule failed: {msg}")
  elapsed "parse" beforeParse
  IO.println s!"bytes={bytes.size} defined_functions={m.funcs.length} imported_functions={m.importedFunctions.length}"
  if mode == "validate" then
    let beforeValidate ← IO.monoNanosNow
    let some mt := Validation.validate? m
      | throw (IO.userError "Validation.validate? returned none")
    elapsed "validate" beforeValidate
    IO.println s!"validated_bodies={m.funcs.length} imports={mt.imports.length} exports={mt.exports.length}"
  return 0
