module

public import SqliteWasm.FunctionVector

@[expose] public section

namespace SqliteWasmArtifact

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary
open Core.Decode (Cursor DecodeM readByte readBlockType readU readVec readSeq readExpr readCode maxLocals)
open Silmaril.Wasm.Component.Chunked (arr runAll readInstrs blockInstr)
open Silmaril.Wasm.Component.ChunkedDecode

def functionCode (function : Func) : CodeEntry := (function.locals, function.body)

def controlBody : Instr → List Instr
  | .block _ body | .loop _ body | .if_ _ body _ => body
  | _ => []

def controlType : Instr → BlockType
  | .block bt _ | .loop bt _ | .if_ bt _ _ => bt
  | _ => .empty

private theorem sliceAt {source : KBytes} (wf : source.wf = true) {start stop : Nat}
    (order : start ≤ stop) (bound : stop ≤ source.len) :
    At source.toList start (bytesBetween source start stop) ∧
    (bytesBetween source start stop).length = stop - start := by
  have fit : start + (stop - start) ≤ source.len := by omega
  have length : (bytesBetween source start stop).length = stop - start := by
    change (source.slice start (stop - start)).toList.length = _
    rw [KBytes.length_toList _ (source.wf_slice _ _ wf fit), source.len_slice]
  refine ⟨⟨?_, ?_⟩, length⟩
  · rw [length]
    exact (source.toList_slice _ _ wf fit).symm
  · rwa [length, source.length_toList wf]

private theorem readAt {α : Type} {source : KBytes} (wf : source.wf = true)
    {start stop : Nat} (order : start ≤ stop) (bound : stop ≤ source.len)
    {reader : DecodeM α} (frame : Frame reader) {value : α}
    (checked : runAll reader (bytesBetween source start stop) = some value) :
    reader ⟨arr source.toList, start⟩ = .ok (value, ⟨arr source.toList, stop⟩) := by
  have slice := sliceAt wf order bound
  have read := run_of_runAll frame checked slice.1
  rwa [slice.2, show start + (stop - start) = stop by omega] at read

/-- A checked run of instructions prepended to a successful continuation at `stop`. -/
def ExprPrefix (source : KBytes) (start stop : Nat) (xs : List Instr) : Prop :=
  ∀ {fuel : Nat} {ys : List Instr} {term : UInt8} {next : Cursor}, 0 < fuel →
    readSeq fuel ⟨arr source.toList, stop⟩ = .ok ((ys, term), next) →
    readSeq (fuel + (stop - start)) ⟨arr source.toList, start⟩ = .ok ((xs ++ ys, term), next)

theorem ExprPrefix.nil {source : KBytes} {pos : Nat} : ExprPrefix source pos pos [] := by
  intro _ _ _ _ _ next
  simpa only [Nat.sub_self, Nat.add_zero, List.nil_append] using next

theorem ExprPrefix.append {source : KBytes} {start middle stop : Nat} {xs ys : List Instr}
    (order : start ≤ middle ∧ middle ≤ stop) (left : ExprPrefix source start middle xs)
    (right : ExprPrefix source middle stop ys) : ExprPrefix source start stop (xs ++ ys) := by
  intro fuel rest term next positive follows
  have joined := left (by omega) (right positive follows)
  rwa [← List.append_assoc,
    show fuel + (stop - middle) + (middle - start) = fuel + (stop - start) by omega] at joined

theorem ExprPrefix.ofRun {source : KBytes} (wf : source.wf = true) {start stop : Nat} {xs : List Instr}
    (order : start ≤ stop) (bound : stop ≤ source.len)
    (checked : runAll (readInstrs (stop - start + 1)) (bytesBetween source start stop) = some xs) :
    ExprPrefix source start stop xs := by
  have slice := sliceAt wf order bound
  intro fuel rest term next positive follows
  have follows' : readSeq fuel ⟨arr source.toList, start + (bytesBetween source start stop).length⟩ =
      .ok ((rest, term), next) := by
    rwa [slice.2, show start + (stop - start) = stop by omega]
  unfold runAll at checked
  split at checked
  · rename_i parsed cursor ran
    split at checked
    · rename_i exactLength
      cases checked
      have result := readSeq_of_readInstrs slice.1 follows' (stop - start + 1) 0
        (Nat.zero_le _) ran exactLength (fuel + (stop - start)) (by omega) (by omega)
      simpa only [Nat.add_zero] using result
    · cases checked
  · cases checked

/-- A sequence with its terminator, consuming exactly `[start, stop)`. -/
def ExprRun (source : KBytes) (start stop : Nat) (is : List Instr) (term : UInt8) : Prop :=
  readSeq (stop - start) ⟨arr source.toList, start⟩ =
    .ok ((is, term), ⟨arr source.toList, stop⟩)

theorem ExprPrefix.finish {source : KBytes} (wf : source.wf = true) {start last : Nat}
    {is : List Instr} {term : UInt8} (order : start ≤ last) (bound : last + 1 ≤ source.len)
    (code : ExprPrefix source start last is)
    (lastByte : runAll readByte (bytesBetween source last (last + 1)) = some term)
    (terminator : (term == 0x0B || term == 0x05) = true) :
    ExprRun source start (last + 1) is term := by
  have tail := readSeq_term (F := 0) (readAt wf (Nat.le_succ _) bound frame_readByte lastByte) terminator
  have finished := code (by decide : 0 < 1) tail
  rw [List.append_nil, show 1 + (last - start) = last + 1 - start by omega] at finished
  exact finished

private theorem extendFuel {source : KBytes} {start stop fuel : Nat} {is : List Instr} {term : UInt8}
    (run : ExprRun source start stop is term) (fits : stop - start ≤ fuel) :
    readSeq fuel ⟨arr source.toList, start⟩ = .ok ((is, term), ⟨arr source.toList, stop⟩) :=
  le_apply (readSeq_mono _ _ fits).2 run

/-- Lift a split block, loop or if without an else marker. The subtree accounts for the
bytes after the block type through the matching end marker. -/
theorem ExprPrefix.control {source : KBytes} (wf : source.wf = true) {start bodyStart stop : Nat}
    {op : UInt8} {bt : BlockType} {is : List Instr} {instr : Instr}
    (headFits : start + 2 ≤ bodyStart) (bodyFits : bodyStart < stop) (bound : stop ≤ source.len)
    (opcode : runAll readByte (bytesBetween source start (start + 1)) = some op)
    (header : runAll readBlockType (bytesBetween source (start + 1) bodyStart) = some bt)
    (body : ExprRun source bodyStart stop is 0x0B) (shape : blockInstr op bt is = some instr) :
    ExprPrefix source start stop [instr] := by
  have readOp := readAt wf (Nat.le_succ _) (by omega) frame_readByte opcode
  have readType := readAt wf (by omega) (by omega) frame_readBlockType header
  intro fuel rest term next positive follows
  let inner := fuel + (stop - start) - 2
  have bodyRun := extendFuel body (fuel := inner) (by dsimp [inner]; omega)
  have instrRun := readInstr_block readType bodyRun shape
  have follows' := le_apply (readSeq_mono fuel (inner + 1) (by dsimp [inner]; omega)).2 follows
  have step := readSeq_step readOp (blockInstr_op shape) instrRun follows'
  change readSeq (inner + 1 + 1) _ = _ at step
  rwa [show inner + 1 + 1 = fuel + (stop - start) by dsimp [inner]; omega] at step

/-- Check the size and locals prefixes and combine them with the terminated expression run.
The resulting equation uses the same Core `readCode` on the original input. -/
theorem readCode_of_parts {source : KBytes} (wf : source.wf = true)
    {start afterSize exprStart stop : Nat} {groups : List (Nat × ValType)} {locals : List ValType}
    {is : List Instr} (order : start ≤ afterSize ∧ afterSize ≤ exprStart ∧ exprStart ≤ stop)
    (bound : stop ≤ source.len)
    (size : runAll (readU 32) (bytesBetween source start afterSize) = some (stop - afterSize))
    (localGroups : runAll (readVec groupR) (bytesBetween source afterSize exprStart) = some groups)
    (expand : (groups.map fun p => List.replicate p.1 p.2).flatten = locals)
    (cap : locals.length ≤ maxLocals) (body : ExprRun source exprStart stop is 0x0B) :
    readCode ⟨source.toByteArray, start⟩ = .ok ((locals, is), ⟨source.toByteArray, stop⟩) := by
  change readCode ⟨arr source.toList, start⟩ = _
  have sizeRun := readAt wf order.1 (by omega) (frame_readU 32) size
  have groupsRun := readAt wf order.2.1 (by omega) (frame_readVec frame_groupR) localGroups
  have available := source.length_toList wf
  have readBody : readExpr ⟨arr source.toList, exprStart⟩ = .ok (is, ⟨arr source.toList, stop⟩) := by
    unfold readExpr
    rw [bind_ok (remaining_apply _), arr_size]
    have fits : stop - exprStart ≤ source.toList.length - exprStart + 1 := by omega
    rw [bind_ok (extendFuel body fits)]
    rfl
  unfold readCode
  rw [bind_ok sizeRun, bind_ok (remaining_apply _)]
  simp only [arr_size, show stop - afterSize ≤ source.toList.length - afterSize by omega, ↓reduceIte]
  change (readVec groupR >>= _) _ = _
  rw [bind_ok groupsRun, foldl_add_fst, Nat.zero_add, expand]
  simp only [cap, ↓reduceIte]
  rw [bind_ok readBody, bind_ok (remaining_apply _)]
  simp only [arr_size, show source.toList.length - afterSize - (source.toList.length - stop) =
    stop - afterSize by omega, beq_self_eq_true, ↓reduceIte, List.flatMap_def, expand]
  rfl

/-- Locate a defined-function ordinal using the original Code envelope, vector count and
preceding size prefixes. The cursor returned by `section?` bounds each skip to the section. -/
def codeFrameAt? (source : Packed.Cursor) (ordinal : Nat) : Option (Nat × Nat) := do
  let spans ← sectionSpans? source
  let (base, _) ← spans.lookup 10
  let code ← section? source spans 10
  ((do
    let count ← Packed.readU 32
    unless ordinal < count do Packed.decodeError "code ordinal out of range"
    repeatEntry (do skip (← Packed.readU 32)) ordinal
    let start := (← get).pos
    skip (← Packed.readU 32)
    return (base + start, base + (← get).pos)).run' code).toOption

/-- The original Code record at a defined-function ordinal decodes to the stated locals
and instruction tree and consumes exactly the record's framed bytes. -/
def ReadsCodeAt (source : Packed.Cursor) (ordinal : Nat) (code : CodeEntry) : Prop :=
  ∃ start stop, codeFrameAt? source ordinal = some (start, stop) ∧
    readCode ⟨source.source.toByteArray, start⟩ = .ok (code, ⟨source.source.toByteArray, stop⟩)

end SqliteWasmArtifact
