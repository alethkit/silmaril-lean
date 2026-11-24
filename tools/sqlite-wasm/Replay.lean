module

public meta import SqliteWasm.VersionModel
public meta import Silmaril.Wasm.Binaryen.Exe.Decode
public meta import Silmaril.Wasm.ModuleParts.Defs

meta section

open SqliteWasm Silmaril.Wasm Silmaril.Wasm.Execution.Core

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def evaluateVersion : Option Nat := do
  let (_, _, .normal [value]) ← runVersion ({} : Store Unit) {} | none
  (Binaryen.asInt .i32 value).map BitVec.toNat

public def main (args : List String) : IO Unit := do
  let [source, output, versionOutput] := args
    | throw (IO.userError "expected original Wasm, re-encoded Wasm and version-result paths")
  let original ← IO.FS.readBinFile source
  let sourceObject ← IO.ofExcept (Binary.Core.Decode.decodeModule original)
  let canonical ← IO.ofExcept (Binaryen.Exe.encodeModule original sqlite)
  let sourceCanonical ← IO.ofExcept (Binaryen.Exe.encodeModule original sourceObject)
  require (canonical == sourceCanonical) "assembled object and original decode encode differently"
  let reparsed ← IO.ofExcept (Binary.Core.Decode.decodeModule canonical)
  let canonicalAgain ← IO.ofExcept (Binaryen.Exe.encodeModule canonical reparsed)
  require (canonicalAgain == canonical) "canonical re-encoding is not stable"
  IO.println s!"Assembled object, full decode and canonical re-decode encode to the same {canonical.size} bytes"

  if canonical == original then
    IO.println s!"Exact re-encoding ({original.size} bytes)"
  else
    let originalBytes := original.data.toList
    let canonicalDiff := Binaryen.Exe.firstDiff originalBytes canonical.data.toList 0
    IO.println s!"Canonical re-encoding differs at byte {canonicalDiff} ({canonical.size} vs {original.size} bytes)"
    let padded ← IO.ofExcept (Binaryen.Exe.encodeModuleP? original sqlite)
    if padded == originalBytes then
      IO.println s!"Exact padded re-encoding ({original.size} bytes)"
    else
      let paddedDiff := Binaryen.Exe.firstDiff originalBytes padded 0
      IO.println s!"Padded re-encoding differs at byte {paddedDiff} ({padded.length} vs {original.size} bytes)"
  IO.FS.writeBinFile output canonical

  require (sqlite.imports.length == 23 && sqlite.importedFunctions.length == 23 &&
    sqlite.funcs.length == 1533) "unexpected function index space"
  let some index := Idx.ofNat? (kind := .func) versionIndex
    | throw (IO.userError "bad function index")
  require ((sqlite.exports.find? (fun e => e.name == "sqlite3_libversion_number")).map Export.index ==
    some (.func index)) "unexpected version export"
  require (sqlite.functionSignature? index == some ⟨[], [.num (.int .i32)]⟩)
    "unexpected version function signature"
  let some value := evaluateVersion
    | throw (IO.userError "Lean interpreter did not return one i32")
  require (value == versionNumber.toNat) "version differs from the SQLite version number model"
  IO.FS.writeFile versionOutput s!"{value}\n"
  IO.println s!"Function {versionIndex} via the Lean interpreter: {value}"
