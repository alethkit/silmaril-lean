module

import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Wasm.ModuleParts.Defs
import Silmaril.Wasm.Validation.Check.Validate
meta import Silmaril.Wasm.Binary.Core.Decode
meta import Silmaril.Wasm.ModuleParts.Defs
meta import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm

private def require (ok : Bool) (message : String) : IO Unit := do
  unless ok do throw (IO.userError message)

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the pinned adler32.wasm path")
  let bytes ← IO.FS.readBinFile path
  let m ← IO.ofExcept (Binary.Core.Decode.decodeModule bytes)
  require (Validation.validate? m).isSome "Core validator rejected the fixture"
  require (bytes.size == 1137 && m.imports.isEmpty && m.funcs.length == 2 &&
    m.memories.length == 1 && m.exports.length == 3 && m.start.isNone)
    "unexpected Core module shape"
  let i32 : ValType := .num (.int .i32)
  let expectedSignature : FuncType := ⟨[i32, i32, i32], [i32]⟩
  for (name, ordinal) in [("adler32_z", 0), ("adler32", 1)] do
    let some index := Idx.ofNat? (kind := .func) ordinal
      | throw (IO.userError "invalid function index")
    require ((m.exports.find? (fun e => e.name == name)).map Export.index == some (.func index) &&
      m.functionSignature? index == some expectedSignature) s!"unexpected export {name}"
  require ((m.exports.find? (fun e => e.name == "memory")).map Export.index ==
    some (.memory ⟨0⟩))
    "missing memory export"
  let truncated := bytes.extract 0 (bytes.size - 1)
  require (Binary.Core.Decode.decodeModule truncated).isOk.not
    "Core decoder accepted a truncated code section"
  IO.println s!"Core decode and validation passed ({bytes.size} bytes, {m.funcs.length} functions)"
