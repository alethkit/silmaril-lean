module

public meta import SqliteWebWasm.Object
public meta import Silmaril.Wasm.Binaryen.Exe.Decode

meta section

open Silmaril.Wasm

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

public def main (args : List String) : IO Unit := do
  let [input, output] := args | throw (IO.userError "expected original and canonical Wasm paths")
  let original ← IO.FS.readBinFile input
  let decoded ← IO.ofExcept (Binary.Core.Decode.decodeModule original)
  let assembled := SqliteWebWasm.sqlite
  require (assembled.funcs.length == 2706 && assembled.imports.length == 36 &&
    assembled.importedFunctions.length == 35 && assembled.exports.length == 267)
    "unexpected web module interface"
  let some entry := assembled.start | throw (IO.userError "missing Wasm start")
  require (entry.toNat == SqliteWebWasm.entrypointIndex) "start index mismatch"
  IO.println s!"start section: function {entry.toNat}"
  for name in ["__wasm_call_ctors", "sqlite3_libversion_number", "sqlite3_open_v2"] do
    let some ⟨_, .func fn⟩ := assembled.exports.find? (·.name == name)
      | throw (IO.userError s!"missing function export {name}")
    IO.println s!"{name}: function {fn.toNat}"
  require (Binaryen.Exe.hasDataCountSection original && assembled.data.length == 428)
    "unexpected data-count section or data-segment count"
  IO.println s!"data segments: {assembled.data.length}, code uses data indices: {Binaryen.Exe.usesDataIdx assembled}"
  let canonical ← IO.ofExcept (Binaryen.Exe.encodeModule original assembled)
  require ((← IO.ofExcept (Binaryen.Exe.encodeModule original decoded)) == canonical)
    "assembled object and full decode encode differently"
  let reparsed ← IO.ofExcept (Binary.Core.Decode.decodeModule canonical)
  require ((← IO.ofExcept (Binaryen.Exe.encodeModule canonical reparsed)) == canonical)
    "canonical re-encoding is not stable"
  unless canonical == original do
    let diff := Binaryen.Exe.firstDiff original.data.toList canonical.data.toList 0
    throw (IO.userError s!"web artifact replay differs at byte {diff}")
  IO.println s!"Exact byte replay: {original.size} bytes"
  IO.FS.writeBinFile output canonical
