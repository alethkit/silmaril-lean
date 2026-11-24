module

public import SqliteWasm.FunctionVector
public meta import Silmaril.Prelude.Bytes.Elab.Defs
public meta import Silmaril.Wasm.Component.Chunked.Defs
public meta import Silmaril.Wasm.Binary.Core.Decode
public meta import Lean.Elab.Term

public meta section

namespace SqliteWasmArtifact

open Lean Elab Term Silmaril
open Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Component.Chunked (CPlan IPlan readLocalsGroup)

private def leafBytes : Nat := 16
private def directEntryBytes : Nat := 128

private def runAt {α : Type} (bytes : ByteArray) (reader : DecodeM α) (pos : Nat) :
    Except String (α × Nat) :=
  (reader.run ⟨bytes, pos⟩).map fun (value, next) => (value, next.pos)

/-- Suggest short runs of whole instructions. Structured instructions are split at their
headers and terminators. The kernel checks the resulting proposal against the original bytes. -/
private partial def instrPlan (bytes : ByteArray) (pos leafStart : Nat) : Except String (IPlan × Nat) := do
  let some op := bytes[pos]? | throw s!"missing instruction at {pos}"
  let flush (rest : IPlan) := if leafStart < pos then IPlan.leaf (pos - leafStart) rest else rest
  if op == 0x0b || op == 0x05 then return (flush .nil, pos)
  if op == 0x02 || op == 0x03 || op == 0x04 then
    let (_, headerEnd) ← runAt bytes readBlockType (pos + 1)
    let (body, terminator) ← instrPlan bytes headerEnd headerEnd
    if op == 0x04 && bytes[terminator]? == some 0x05 then
      let (elseBody, stop) ← instrPlan bytes (terminator + 1) (terminator + 1)
      let (rest, endPos) ← instrPlan bytes (stop + 1) (stop + 1)
      return (flush (.ifElse (headerEnd - pos) body elseBody rest), endPos)
    let (rest, endPos) ← instrPlan bytes (terminator + 1) (terminator + 1)
    return (flush (.block (headerEnd - pos) body rest), endPos)
  let (_, stop) ← runAt bytes (readInstr (bytes.size + 1) op.toNat) (pos + 1)
  if stop - leafStart ≤ leafBytes || leafStart == pos then instrPlan bytes stop leafStart
  else
    let (rest, endPos) ← instrPlan bytes pos pos
    return (flush rest, endPos)

private def codePlan (bytes : ByteArray) (start stop : Nat) : Except String CPlan := do
  let (size, bodyStart) ← runAt bytes (readU 32) start
  let (_, instrStart) ← runAt bytes (readVec readLocalsGroup) bodyStart
  let (body, terminator) ← instrPlan bytes instrStart instrStart
  unless bodyStart + size == stop && terminator + 1 == stop do
    throw s!"code entry at {start} does not end at {stop}"
  return ⟨bodyStart - start, instrStart - bodyStart, body⟩

private partial def planSyntax : IPlan → TermElabM Term
  | .nil => `(IPlan.nil)
  | .leaf size rest => do `(IPlan.leaf $(quote size) $(← planSyntax rest))
  | .block size body rest => do
    `(IPlan.block $(quote size) $(← planSyntax body) $(← planSyntax rest))
  | .ifElse size body elseBody rest => do
    `(IPlan.ifElse $(quote size) $(← planSyntax body) $(← planSyntax elseBody) $(← planSyntax rest))

/-- Turn proposed entry ends into a list of cuts. Entries above the supplied budget get only
their size prefix checked. Other large entries get instruction-run proposals. -/
syntax "sqlite_code_cuts " str num num "[" num,* "]" : term

elab_rules : term
  | `(sqlite_code_cuts $file:str $budget:num $start:num [$ends:num,*]) => do
    let bytes ← KBytes.Elab.readRelative file.getString
    let mut pos := start.getNat
    let mut cuts := #[]
    for stop in ends.getElems do
      let width := stop.getNat - pos
      let plan ←
        if width > budget.getNat then do
          let (_, bodyStart) ← ofExcept (runAt bytes (readU 32) pos)
          `(CodePlan.skip $(quote (bodyStart - pos)))
        else if width ≤ directEntryBytes then `(CodePlan.direct)
        else do
          let p ← ofExcept (codePlan bytes pos stop.getNat)
          `(CodePlan.split ⟨$(quote p.kSize), $(quote p.kLocals), $(← planSyntax p.body)⟩)
      cuts := cuts.push (← `(($stop, $plan)))
      pos := stop.getNat
    elabTerm (← `(([$cuts,*] : List (Nat × CodePlan)))) none

end SqliteWasmArtifact
