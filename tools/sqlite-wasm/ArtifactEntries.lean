module

public import Silmaril.Prelude.Bytes.Elab.Defs
public import Silmaril.Wasm.Binary.Packed.Defs
public import Silmaril.Wasm.Component.Chunked.Defs
public meta import Lean.Elab.Term
public meta import Lean.Meta.AppBuilder

@[expose] public section

namespace SqliteWasmArtifact

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary
open Silmaril.Wasm.Component.Chunked (runAll)

/-- Advance a packed cursor without constructing the skipped byte slice. -/
def skip (width : Nat) : Packed.Reader Unit := do
  let cursor ← get
  unless cursor.pos + width ≤ cursor.source.len do Packed.decodeError "skip past end"
  set { cursor with pos := cursor.pos + width }

/-- Scan the header and ordered section envelopes of a stripped Core artifact. -/
def sectionSpans? (source : Packed.Cursor) : Option (List (Nat × (Nat × Nat))) :=
  ((do
    Packed.readHeader
    go ((← Packed.remaining) + 1) 0).run' source).toOption
where
  go : Nat → Nat → Packed.Reader (List (Nat × (Nat × Nat)))
    | 0, _ => Packed.decodeError "section scan exhausted"
    | fuel + 1, last => do
      if (← Packed.remaining) == 0 then return []
      let (id, size) ← Packed.sectionPrefix Packed.readByte (Packed.readU 32)
        Packed.remaining Packed.decodeError
      let rank := Core.Decode.sectionRank id
      unless last < rank do Packed.decodeError "unexpected section"
      let start := (← get).pos
      skip size
      return (id, start, size) :: (← go fuel rank)

/-- Construct a bounded cursor for one section of the original. -/
def section? (source : Packed.Cursor) (spans : List (Nat × (Nat × Nat))) (id : Nat) :
    Option Packed.Cursor := do
  let (pos, size) ← spans.lookup id
  ((Packed.readSlice size).run' { source with pos := pos }).toOption

/-- Defined-function lookup in the complete quoted object's index space. -/
def definedFunction? (object : Wasm.Module) (index : Nat) : Option Func :=
  let imported := object.importedFunctions.length
  if index < imported then none else object.funcs[index - imported]?

/-- Run exactly the given number of bounded entry reads. -/
def repeatEntry {α : Type} (entry : Packed.Reader α) : Nat → Packed.Reader Unit
  | 0 => pure ()
  | n + 1 => do
    let _ ← entry
    repeatEntry entry n

def readTypeAt (ordinal : Nat) : Packed.Reader (Nat × TypeIdx) := do
  let count ← Packed.readU 32
  unless ordinal < count do Packed.decodeError "function declaration out of range"
  repeatEntry (Packed.readU 32) ordinal
  let type ← Packed.readU 32
  let some idx := Idx.ofNat? (kind := .type_) type
    | Packed.decodeError "function type index out of range"
  return (count, idx)

def readCodeAt (ordinal expectedCount : Nat) :
    Packed.Reader (List ValType × Wasm.Expr) := do
  let count ← Packed.readU 32
  unless count == expectedCount do Packed.decodeError "function and code counts differ"
  repeatEntry (do skip (← Packed.readU 32)) ordinal
  let start ← get
  let size ← Packed.readU 32
  skip size
  let stop ← get
  let entry := start.source.slice start.pos (stop.pos - start.pos)
  let some decoded := runAll Core.Decode.readCode entry.toList
    | Packed.decodeError "invalid selected code entry"
  return decoded

/-- Resolve a defined function using the artifact's own imports, Function vector and Code
vector. Earlier bodies are skipped by their framed sizes. The selected entry is decoded by
the Core body reader, including its locals, instruction tree and exact size. -/
def sourceFunction? (source : Packed.Cursor) (index : Nat) : Option Func := do
  let spans ← sectionSpans? source
  let imports ← section? source spans 2
  let parsed ← runAll (Core.Decode.readSectionBody 2 {}) imports.source.toList
  let imported := ({ imports := parsed.imports } : Wasm.Module).importedFunctions.length
  if index < imported then none else
    let ordinal := index - imported
    let declarations ← section? source spans 3
    let code ← section? source spans 10
    let (count, type) ← ((readTypeAt ordinal).run' declarations).toOption
    let (locals, body) ← ((readCodeAt ordinal count).run' code).toOption
    return ⟨type, locals, body⟩

/-- Resolve a named function export by scanning bounded export records. Only names of the
requested byte length are compared. A successful lookup consumes the matching record. -/
def sourceExport? (source : Packed.Cursor) (name : String) : Option Nat := do
  let exports ← section? source (← sectionSpans? source) 7
  let found ← ((do go (← Packed.readU 32) name.toUTF8).run' exports).toOption
  found
where
  go : Nat → ByteArray → Packed.Reader (Option Nat)
    | 0, _ => return none
    | count + 1, name => do
      let size ← Packed.readU 32
      let nameMatches ← if size == name.size then do
        let bytes ← Packed.readSlice size
        pure (bytes.source.eqByteArray name)
      else
        skip size
        pure false
      let kind ← Packed.readByte
      let idx ← Packed.readU 32
      if nameMatches && kind == 0 then return some idx
      go count name

/-- Decode the start function index from the artifact's Start section. -/
def sourceStart? (source : Packed.Cursor) : Option FuncIdx := do
  let start ← section? source (← sectionSpans? source) 8
  runAll Core.Decode.readIdx start.source.toList

end SqliteWasmArtifact

end

public meta section

open Lean Elab Command Silmaril

/-- Check a closed equality by submitting reflexivity directly to the kernel.
The elaborator constructs the statement without first reducing the reader. -/
elab "sqlite_check_eq " name:ident " : " statement:term : command => do
  let type ← liftTermElabM do
    let type ← Term.elabType statement
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars type
  let some (_, _, rhs) := type.eq? | throwError "expected an equality"
  let ns ← getCurrNamespace
  liftCoreM do
    let proof ← Meta.MetaM.run' (Meta.mkEqRefl rhs)
    KBytes.Elab.addThm (ns ++ name.getId) type proof
