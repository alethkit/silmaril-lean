module

public import Silmaril.Formats.Compression.Checksum.Adler32
import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binaryen.Interp
meta import Silmaril.Wasm.Binary.Core.Decode
meta import Silmaril.Wasm.Binaryen.Interp

/-! The null-buffer, zero-length path through the decoded `adler32_z` body.
The Core decoder and the shape witness are exercised on the pinned file.
The theorem is about the fuel interpreter on every body matching this shape. -/

public section

namespace ZlibWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

private def i32 : ValType := .num (.int .i32)

/-- The local declarations after the three i32 parameters. -/
def localTypes : List ValType := [i32, i32, i32, i32]

/-- The locals and branch instructions visited by initialization, with the
two unexecuted tails supplied as parameters. -/
def initBody (one more : List Instr) : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 65535, .intBinOp .i32 .and, .localSet ⟨3⟩,
   .localGet ⟨0⟩, .intConst .i32 16, .intBinOp .i32 (.shr .unsigned), .localSet ⟨4⟩,
   .intConst .i32 1, .localSet ⟨0⟩,
   .block .empty (.localGet ⟨2⟩ :: .intConst .i32 1 :: .intRelOp .i32 .ne :: .brIf ⟨0⟩ :: one),
   .block .empty (.localGet ⟨1⟩ :: .intTestOp .i32 .eqz :: .brIf ⟨0⟩ :: more),
   .localGet ⟨0⟩]

/-- The two branch tails are arbitrary because initialization skips them. -/
structure InitWitness (f : Func) where
  one : List Instr
  more : List Instr
  locals_eq : f.locals = localTypes
  body_eq : f.body = initBody one more

/-- Check the fixed instructions and produce the equalities used by the proof. -/
def initWitness? (f : Func) : Option (InitWitness f) :=
  match hl : f.locals, hb : f.body with
  | [.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)],
    [.localGet ⟨0⟩, .intConst .i32 mask, .intBinOp .i32 .and, .localSet ⟨3⟩,
     .localGet ⟨0⟩, .intConst .i32 shift, .intBinOp .i32 (.shr .unsigned), .localSet ⟨4⟩,
     .intConst .i32 initial, .localSet ⟨0⟩,
     .block .empty (.localGet ⟨2⟩ :: .intConst .i32 single :: .intRelOp .i32 .ne :: .brIf ⟨0⟩ :: one),
     .block .empty (.localGet ⟨1⟩ :: .intTestOp .i32 .eqz :: .brIf ⟨0⟩ :: more),
     .localGet ⟨0⟩] =>
    if h : mask = 65535 ∧ shift = 16 ∧ initial = 1 ∧ single = 1 then
      some ⟨one, more, hl, by simpa only [initBody, h.1, h.2.1, h.2.2.1, h.2.2.2] using hb⟩
    else none
  | _, _ => none

/-- Observe the store and returned checksum at fuel 32 for `(seed, 0, 0)`. -/
def initResult {H : Type} (store : Store H) (seed : BitVec 32) (f : Func) :
    Option (Store H × BitVec 32) := do
  let frame := Frame.forCall {} [.i32 seed, .i32 0, .i32 0] f.locals
  let (s, _, .normal [v]) ← Binaryen.run 32 store frame [] (Binaryen.liftInstrs f.body) | none
  return (s, ← Binaryen.asInt .i32 v)

set_option maxRecDepth 3000 in
/-- For all seeds and stores, initialization returns the modeled checksum
of the empty input and preserves the store, provided the shape check succeeds. -/
theorem initialization {H : Type} (s : Store H) (seed : BitVec 32) (f : Func)
    (w : InitWitness f) :
    initResult s seed f =
      some (s, BitVec.ofNat 32 (Silmaril.Formats.Compression.adler32OfList [])) := by
  unfold initResult
  rw [w.locals_eq, w.body_eq]
  rfl

#print axioms initialization

end ZlibWasm

open Silmaril.Wasm

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the pinned adler32.wasm path")
  let bytes ← IO.FS.readBinFile path
  let m ← IO.ofExcept (Binary.Core.Decode.decodeModule bytes)
  let some e := m.exports.find? (fun e => e.name == "adler32_z")
    | throw (IO.userError "missing adler32_z export")
  let .func index := e.index | throw (IO.userError "adler32_z export is not a function")
  let imports := m.importedFunctions.length
  unless index.toNat ≥ imports do throw (IO.userError "adler32_z is imported")
  let some f := m.funcs[index.toNat - imports]?
    | throw (IO.userError "missing defined adler32_z body")
  let some _ := ZlibWasm.initWitness? f
    | throw (IO.userError "decoded adler32_z does not match the initialization witness")
  IO.println "Decoded adler32_z matched the initialization witness"
