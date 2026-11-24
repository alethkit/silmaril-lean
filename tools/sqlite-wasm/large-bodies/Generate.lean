module

public meta import Silmaril.Wasm.Binary.Core.Decode
public meta import Silmaril.Wasm.Component.Chunked.Defs

public meta section

open Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Component.Chunked (readLocalsGroup)

/-- The generator proposes cuts using compiled decoding. The emitted equations check all
these premises on the original packed literal and refer to the existing quotation. -/
private inductive Piece where
  | instructions (start stop first count : Nat)
  | control (start bodyStart terminator index opcode : Nat) (body : List Piece)

private structure Run where
  start : Nat
  stop : Nat
  first : Nat

private def readAt {α : Type} (bytes : ByteArray) (reader : DecodeM α) (pos : Nat) :
    Except String (α × Nat) :=
  (reader.run ⟨bytes, pos⟩).map fun (value, next) => (value, next.pos)

private def flush (pieces : Array Piece) (run : Option Run) (idx : Nat) : Array Piece :=
  match run with
  | none => pieces
  | some r => pieces.push (.instructions r.start r.stop r.first (idx - r.first))

private def runBytes : Nat := 192

private partial def plan (bytes : ByteArray) (pos idx : Nat) (run : Option Run)
    (pieces : Array Piece) : Except String (List Piece × Nat) := do
  let some op := bytes[pos]? | throw s!"missing opcode at {pos}"
  if op == 0x0B || op == 0x05 then return ((flush pieces run idx).toList, pos)
  let (_, next) ← readAt bytes (readInstr (bytes.size + 1) op.toNat) (pos + 1)
  if next - pos > runBytes && (op == 0x02 || op == 0x03 || op == 0x04) then
    let (_, headerStop) ← readAt bytes readBlockType (pos + 1)
    let (children, term) ← plan bytes headerStop 0 none #[]
    if bytes[term]? == some 0x0B && term + 1 == next then
      return ← plan bytes next (idx + 1) none
        ((flush pieces run idx).push (.control pos headerStop term idx op.toNat children))
  let (pieces, run) := match run with
    | some r => if next - r.start ≤ runBytes then (pieces, { r with stop := next })
      else (flush pieces run idx, ⟨pos, next, idx⟩)
    | none => (pieces, ⟨pos, next, idx⟩)
  plan bytes next (idx + 1) (some run) pieces

private structure Segment where
  start : Nat
  stop : Nat
  values : String
  proof : String

private def args (start stop : Nat) : String :=
  s!"(source := originalBytes) (start := {start}) (stop := {stop})"

private def bound : String := "(by rw [originalBytes.len_eq]; decide)"

private def joinProof (stop : Nat) (segments : List Segment) : String :=
  segments.foldr (fun s tail =>
    s!"ExprPrefix.append {args s.start stop} (middle := {s.stop}) (by decide) {s.proof}\n    ({tail})")
    s!"ExprPrefix.nil (source := originalBytes) (pos := {stop})"

private partial def emitSequence (start term : Nat) (expected : String) (pieces : List Piece) : String := Id.run do
  let mut text := ""
  let mut segments := #[]
  for piece in pieces do
    match piece with
    | .instructions a b first count =>
      let values := s!"instructions{a}"
      let proof := s!"prefix{a}"
      text := text ++ s!"private def {values} := ({expected}.drop {first}).take {count}\n\n" ++
        s!"sqlite_check_eq instructionsOk{a} :\n" ++
        s!"  runAll (readInstrs {b - a + 1}) (bytesBetween originalBytes {a} {b}) = some {values}\n\n" ++
        s!"private theorem {proof} : ExprPrefix originalBytes {a} {b} {values} :=\n" ++
        s!"  ExprPrefix.ofRun {args a b} (xs := {values})\n" ++
        s!"    originalBytes.wf_true (by decide) {bound} instructionsOk{a}\n\n"
      segments := segments.push ⟨a, b, values, proof⟩
    | .control a inside finish idx op children =>
      let stop := finish + 1
      let instr := s!"instruction{a}"
      let child := s!"body{inside}"
      let proof := s!"prefix{a}"
      text := text ++ s!"private def {instr} : Instr := ({expected}[{idx}]?).getD .nop\n" ++
        s!"private def {child} := controlBody {instr}\n\n" ++
        emitSequence inside finish child children ++
        s!"sqlite_check_eq opcodeOk{a} : runAll readByte (bytesBetween originalBytes {a} {a+1}) = some {op}\n\n" ++
        s!"sqlite_check_eq headerOk{a} :\n" ++
        s!"  runAll readBlockType (bytesBetween originalBytes {a+1} {inside}) = some (controlType {instr})\n\n" ++
        s!"sqlite_check_eq shapeOk{a} : blockInstr {op} (controlType {instr}) {child} = some {instr}\n\n" ++
        s!"private theorem {proof} : ExprPrefix originalBytes {a} {stop} [{instr}] :=\n" ++
        s!"  ExprPrefix.control {args a stop} (bodyStart := {inside})\n" ++
        s!"    originalBytes.wf_true (by decide) (by decide) {bound}\n" ++
        s!"    opcodeOk{a} headerOk{a} expression{inside} shapeOk{a}\n\n"
      segments := segments.push ⟨a, stop, s!"[{instr}]", proof⟩
  let names := ", ".intercalate (segments.toList.map (·.values))
  text := text ++ s!"private def pieces{start} : List Instr := List.flatten [{names}]\n\n" ++
    s!"sqlite_check_eq piecesOk{start} : pieces{start} = {expected}\n\n" ++
    s!"private theorem piecesRead{start} : ExprPrefix originalBytes {start} {term} pieces{start} :=\n" ++
    s!"  {joinProof term segments.toList}\n\n" ++
    s!"sqlite_check_eq endOk{term} : runAll readByte (bytesBetween originalBytes {term} {term+1}) = some 0x0B\n\n" ++
    s!"private theorem expression{start} : ExprRun originalBytes {start} {term+1} {expected} 0x0B := by\n" ++
    s!"  rw [← piecesOk{start}]\n" ++
    s!"  exact ExprPrefix.finish (start := {start}) (last := {term}) originalBytes.wf_true\n" ++
    s!"    (by decide) {bound} piecesRead{start} endOk{term} (by decide)\n\n"
  return text

private structure Target where
  ordinal : Nat
  start : Nat
  stop : Nat
  quotedPart : String
  index : Nat

private def targets : List Target :=
  [⟨99, 38354, 76747, "Code0099", 0⟩, ⟨260, 134349, 148373, "Code0240", 20⟩,
   ⟨719, 311161, 325196, "Code0719", 0⟩, ⟨767, 348781, 364946, "Code0767", 0⟩]

private def emitBody (bytes : ByteArray) (t : Target) : Except String String := do
  let (size, afterSize) ← readAt bytes (readU 32) t.start
  let (groups, exprStart) ← readAt bytes (readVec readLocalsGroup) afterSize
  let (pieces, term) ← plan bytes exprStart 0 none #[]
  unless bytes[term]? == some 0x0B && term + 1 == t.stop && afterSize + size == t.stop do
    throw s!"invalid code frame proposal at ordinal {t.ordinal}"
  return "module\n\npublic import SqliteWasm.BodyComposition\npublic import SqliteWasm.Original\n" ++
    s!"public import SqliteWasm.Object\n\npublic section\n\nnamespace SqliteWasm.LargeBody{t.ordinal}\n\n" ++
    "open SqliteWasm\n" ++
    "open SqliteWasmArtifact Silmaril.Wasm\n" ++
    "open Silmaril.Wasm.Binary.Core.Decode (readByte readBlockType readU readVec maxLocals)\n" ++
    "open Silmaril.Wasm.Component.Chunked (runAll readInstrs blockInstr)\n" ++
    "open Silmaril.Wasm.Component.ChunkedDecode (groupR)\n\n" ++
    "set_option maxRecDepth 65536\nset_option maxHeartbeats 2000000\n\n" ++
    s!"private def quoted := ({t.quotedPart}.funcs.map functionCode)[{t.index}]!\n" ++
    "private def body : List Instr := quoted.2\n\n" ++
    emitSequence exprStart term "body" pieces ++
    s!"sqlite_check_eq originalFrame : codeFrameAt? original {t.ordinal} = some ({t.start}, {t.stop})\n\n" ++
    s!"sqlite_check_eq sizeOk : runAll (readU 32) (bytesBetween originalBytes {t.start} {afterSize}) =\n" ++
    s!"  some ({t.stop} - {afterSize})\n\n" ++
    "private noncomputable def groups :=\n" ++
    s!"  (runAll (readVec groupR) (bytesBetween originalBytes {afterSize} {exprStart})).getD []\n\n" ++
    s!"sqlite_check_eq groupsOk : runAll (readVec groupR) (bytesBetween originalBytes {afterSize} {exprStart}) = some groups\n\n" ++
    "sqlite_check_eq localsOk : (groups.map fun p => List.replicate p.1 p.2).flatten = quoted.1\n\n" ++
    s!"sqlite_check_eq localsLength : quoted.1.length = {groups.flatten.length}\n\n" ++
    "private theorem localsFit : quoted.1.length ≤ maxLocals := by rw [localsLength]; decide\n\n" ++
    s!"sqlite_check_eq quoteOrdinal : (sqlite.funcs.map functionCode)[{t.ordinal}]! = quoted\n\n" ++
    s!"theorem originalCode : ReadsCodeAt original {t.ordinal} (sqlite.funcs.map functionCode)[{t.ordinal}]! := by\n" ++
    "  rw [quoteOrdinal]\n" ++
    s!"  refine ⟨{t.start}, {t.stop}, originalFrame, ?_⟩\n" ++
    s!"  exact readCode_of_parts {args t.start t.stop} (afterSize := {afterSize}) (exprStart := {exprStart})\n" ++
    s!"    originalBytes.wf_true (by decide) {bound} sizeOk groupsOk localsOk localsFit expression{exprStart}\n\n" ++
    s!"#print axioms originalCode\n\nend SqliteWasm.LargeBody{t.ordinal}\n"

public def main (args : List String) : IO Unit := do
  let wasm :: out :: requested := args
    | throw (IO.userError "expected Wasm path, generated source directory, and optional ordinals")
  let bytes ← IO.FS.readBinFile wasm
  for ordinal in requested do
    unless targets.any (fun t => toString t.ordinal == ordinal) do
      throw (IO.userError s!"unsupported ordinal {ordinal}")
  for target in targets do
    if requested.isEmpty || requested.contains (toString target.ordinal) then
      let name := s!"LargeBody{target.ordinal}"
      IO.FS.writeFile (System.FilePath.mk out / s!"{name}.lean") (← IO.ofExcept (emitBody bytes target))
      IO.println name
