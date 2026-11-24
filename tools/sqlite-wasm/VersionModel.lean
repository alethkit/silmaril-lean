module

public import SqliteWasm.Object
public import Silmaril.Wasm.Binaryen.Interp

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- Resolve the pinned version export to a locally defined function. -/
def versionFunction? : Option Func := do
  let exp ← sqlite.exports.find? (fun e => e.name == "sqlite3_libversion_number")
  let .func index := exp.index | none
  let imported := sqlite.importedFunctions.length
  if index.toNat < imported then none
  else sqlite.funcs[index.toNat - imported]?

/-- The SQLite version number convention applied to the pinned release. -/
def versionNumber : BitVec 32 := BitVec.ofNat 32 (3 * 1000000 + 54 * 1000 + 1)

/-- Execute the selected body on an empty operand stack using the fuel interpreter. -/
def runVersion {H : Type} (store : Store H) (frame : Frame) : Option (Store H × Frame × Binaryen.Flow) := do
  let fn ← versionFunction?
  Binaryen.run 2 store frame [] (Binaryen.liftInstrs fn.body)

end SqliteWasm
