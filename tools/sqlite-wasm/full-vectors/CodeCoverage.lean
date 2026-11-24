module

public import SqliteWasm.BodyComposition

@[expose] public section

namespace SqliteWasmArtifact

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary
open Core.Decode (Cursor readU readVec readCount readCode readBytes)
open Silmaril.Wasm.Component.Chunked (arr runAll)
open Silmaril.Wasm.Component.ChunkedDecode

private theorem readCountPrefix {source : KBytes} (wf : source.wf = true)
    {start stop : Nat} {value : Nat} (order : start ≤ stop) (bound : stop ≤ source.len)
    (checked : runAll (readU 32) (bytesBetween source start stop) = some value) :
    readU 32 ⟨source.toByteArray, start⟩ = .ok (value, ⟨source.toByteArray, stop⟩) := by
  have fit : start + (stop - start) ≤ source.len := by omega
  have length : (bytesBetween source start stop).length = stop - start := by
    change (source.slice start (stop - start)).toList.length = _
    rw [KBytes.length_toList _ (source.wf_slice _ _ wf fit), source.len_slice]
  have atStart : At source.toList start (bytesBetween source start stop) := by
    constructor
    · rw [length]
      exact (source.toList_slice _ _ wf fit).symm
    · rwa [length, source.length_toList wf]
  have read := run_of_runAll (frame_readU 32) checked atStart
  rwa [length, show start + (stop - start) = stop by omega] at read

/-- A checked size field, retaining the original absolute start and end cursors. -/
def CodeFrame (bytes : ByteArray) (start stop : Nat) : Prop :=
  ∃ afterSize, start ≤ afterSize ∧ afterSize ≤ stop ∧ stop ≤ bytes.size ∧
    readU 32 ⟨bytes, start⟩ = .ok (stop - afterSize, ⟨bytes, afterSize⟩)

private theorem CodeFrame.skip {bytes : ByteArray} {start stop : Nat}
    (frame : CodeFrame bytes start stop) :
    readCodeSlot false ⟨bytes, start⟩ = .ok (none, ⟨bytes, stop⟩) := by
  obtain ⟨afterSize, _, ordered, bound, prefixRun⟩ := frame
  have consumed : afterSize + (stop - afterSize) = stop := by omega
  simp only [readCodeSlot, Bool.false_eq_true, ↓reduceIte]
  rw [bind_ok prefixRun, bind_apply, readBytes_apply]
  simp only [consumed, bound]
  rfl

private theorem CodeFrame.readEnd {bytes : ByteArray} {start stop : Nat} {code : CodeEntry}
    {next : Cursor} (frame : CodeFrame bytes start stop)
    (read : readCode ⟨bytes, start⟩ = .ok (code, next)) : next = ⟨bytes, stop⟩ := by
  obtain ⟨afterSize, prefixOrder, order, bound, prefixRun⟩ := frame
  have nextBound := frame_readCode.self read (by change start ≤ bytes.size; omega)
  unfold readCode at read
  rw [bind_ok prefixRun, bind_ok (remaining_apply _)] at read
  have sizeFits : stop - afterSize ≤ bytes.size - afterSize := by omega
  simp only [sizeFits, ↓reduceIte] at read
  change ((readVec groupR) >>= _) _ = _ at read
  obtain ⟨groups, localsEnd, localsRun, rest⟩ := ok_bind read
  split at rest
  · obtain ⟨body, bodyEnd, bodyRun, finished⟩ := ok_bind rest
    rw [bind_ok (remaining_apply _)] at finished
    split at finished
    · rename_i exactSize
      change Except.ok (_, bodyEnd) = Except.ok (code, next) at finished
      have endEq := congrArg Prod.snd (Except.ok.inj finished)
      change bodyEnd = next at endEq
      subst next
      have localsAdvance := mono_apply (mono_readVec (show Mono groupR by unfold groupR; mono_tac)) localsRun
      have bodyAdvance := mono_apply mono_readExpr bodyRun
      have sameBytes := nextBound.1
      change bodyEnd.bytes = bytes at sameBytes
      have endsInInput := nextBound.2
      rw [sameBytes] at endsInInput exactSize
      simp only [beq_iff_eq] at exactSize
      have endPos : bodyEnd.pos = stop := by simp only at exactSize localsAdvance; omega
      cases bodyEnd
      simp only at sameBytes endPos
      subst_vars
      rfl
    · obtain ⟨_, _, failed, _⟩ := ok_bind finished
      exact (decodeError_ne_ok _ _ _ failed).elim
  · obtain ⟨_, _, failed, _⟩ := ok_bind rest
    exact (decodeError_ne_ok _ _ _ failed).elim

/-- A framing trace accounts for every record in byte order. -/
inductive CodeFrames (bytes : ByteArray) : Nat → Nat → List (Nat × Nat) → Prop where
  | nil (pos : Nat) : CodeFrames bytes pos pos []
  | cons {a b z : Nat} {tail : List (Nat × Nat)} :
      CodeFrame bytes a b → CodeFrames bytes b z tail → CodeFrames bytes a z ((a, b) :: tail)

/-- The plan proposes the end of each size prefix and the end of each record. -/
def checkFrames (source : KBytes) (stop : Nat) : Nat → List (Nat × Nat) → Bool
  | pos, [] => pos == stop
  | pos, (afterSize, next) :: tail =>
      decide (pos ≤ afterSize ∧ afterSize ≤ next ∧ next ≤ source.len) &&
      (runAll (readU 32) (bytesBetween source pos afterSize) == some (next - afterSize)) &&
      checkFrames source stop next tail

def frameSpans : Nat → List (Nat × Nat) → List (Nat × Nat)
  | _, [] => []
  | pos, p :: tail => (pos, p.2) :: frameSpans p.2 tail

/-- A successful framing check uses only the original bounded packed size slices. -/
theorem checkFrames_sound {source : KBytes} (wf : source.wf = true) {start stop : Nat}
    {plan : List (Nat × Nat)} (checked : checkFrames source stop start plan = true) :
    CodeFrames source.toByteArray start stop (frameSpans start plan) := by
  induction plan generalizing start with
  | nil =>
    have eq : start = stop := beq_iff_eq.mp checked
    subst start
    exact CodeFrames.nil stop
  | cons p tail ih =>
    obtain ⟨afterSize, next⟩ := p
    simp only [checkFrames, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at checked
    obtain ⟨⟨⟨ordered, headFits, bodyFits⟩, size⟩, rest⟩ := checked
    have bytesLength : source.toByteArray.size = source.len := source.length_toList wf
    exact CodeFrames.cons ⟨afterSize, ordered, headFits, bytesLength ▸ bodyFits,
      readCountPrefix wf ordered (by omega) size⟩ (ih rest)

/-- Full Code reads for just the slots omitted by the masked vector. -/
def GapReads (bytes : ByteArray) (mask : List Bool) (funcs : List Func)
    (frames : List (Nat × Nat)) : Prop :=
  ∀ {i : Nat} {f : Func} {a b : Nat},
    mask[i]? = some false → funcs[i]? = some f → frames[i]? = some (a, b) →
    readCode ⟨bytes, a⟩ = .ok (functionCode f, ⟨bytes, b⟩)

private theorem fillSlots {bytes : ByteArray} {start stop : Nat} {frames : List (Nat × Nat)}
    (trace : CodeFrames bytes start stop frames) {mask : List Bool} {funcs : List Func}
    (maskLen : mask.length = funcs.length) (frameLen : mask.length = frames.length)
    (gaps : GapReads bytes mask funcs frames)
    (masked : readCodeSlots mask ⟨bytes, start⟩ = .ok (projectCode mask funcs, ⟨bytes, stop⟩)) :
    readVec.go readCode funcs.length ⟨bytes, start⟩ = .ok (funcs.map functionCode, ⟨bytes, stop⟩) := by
  induction trace generalizing mask funcs with
  | nil =>
    cases mask <;> cases funcs <;> simp_all [readVec.go]
    rfl
  | @cons a b z tail frame chain ih =>
    cases mask with
    | nil => simp at frameLen
    | cons flag mask =>
      cases funcs with
      | nil => simp at maskLen
      | cons f funcs =>
        have tailGaps : GapReads bytes mask funcs tail := by
          intro i f p q off func place
          exact gaps (i := i + 1) off func place
        have mlen : mask.length = funcs.length := Nat.succ.inj maskLen
        have flen : mask.length = tail.length := Nat.succ.inj frameLen
        simp only [readCodeSlots] at masked
        unfold projectCode at masked
        simp only [List.zipWith_cons_cons] at masked
        cases flag with
        | false =>
          rw [bind_ok frame.skip] at masked
          obtain ⟨xs, next, rest, done⟩ := ok_bind masked
          cases done
          have read := gaps (i := 0) (f := f) (a := a) (b := b) rfl rfl rfl
          rw [List.length_cons, readVec_go_succ, bind_ok read, bind_ok (ih mlen flen tailGaps rest)]
          rfl
        | true =>
          obtain ⟨slot, middle, head, more⟩ := ok_bind masked
          change (some <$> readCode) ⟨bytes, a⟩ = .ok (slot, middle) at head
          rw [show (some <$> readCode) ⟨bytes, a⟩ =
            (fun p : CodeEntry × Cursor => (some p.1, p.2)) <$> readCode ⟨bytes, a⟩ from rfl] at head
          cases read : readCode ⟨bytes, a⟩ with
          | error => simp [read] at head
          | ok pair =>
            obtain ⟨body, next⟩ := pair
            rw [read] at head
            cases head
            have atEnd := frame.readEnd read
            subst next
            obtain ⟨xs, next, rest, done⟩ := ok_bind more
            cases done
            rw [List.length_cons, readVec_go_succ, bind_ok read, bind_ok (ih mlen flen tailGaps rest)]
            rfl

/-- Replace every framing-only slot with its separately verified `readCode` run. -/
theorem readFullCodeVector {source : KBytes} (wf : source.wf = true) {start entries stop : Nat}
    {frames : List (Nat × Nat)} {mask : List Bool} {funcs : List Func}
    (ordered : start ≤ entries) (countFits : entries + mask.length ≤ source.len)
    (count : runAll (readU 32) (bytesBetween source start entries) = some mask.length)
    (maskLen : mask.length = funcs.length) (frameLen : mask.length = frames.length)
    (trace : CodeFrames source.toByteArray entries stop frames)
    (gaps : GapReads source.toByteArray mask funcs frames)
    (masked : readCodeVector mask ⟨source.toByteArray, start⟩ =
      .ok (projectCode mask funcs, ⟨source.toByteArray, stop⟩)) :
    (readVec readCode) ⟨source.toByteArray, start⟩ =
      .ok (funcs.map functionCode, ⟨source.toByteArray, stop⟩) := by
  have prefixRun := readCountPrefix wf ordered (by omega) count
  change readU 32 ⟨arr source.toList, start⟩ =
    .ok (mask.length, ⟨arr source.toList, entries⟩) at prefixRun
  have countRun := readCount_at (k := entries - start)
    (by rwa [show start + (entries - start) = entries by omega])
    (by rw [show start + (entries - start) = entries by omega, source.length_toList wf]; omega)
  rw [show start + (entries - start) = entries by omega] at countRun
  change readCount ⟨source.toByteArray, start⟩ =
    .ok (mask.length, ⟨source.toByteArray, entries⟩) at countRun
  unfold readCodeVector at masked
  rw [bind_ok countRun] at masked
  simp only [↓reduceIte] at masked
  unfold readVec
  rw [bind_ok countRun, maskLen]
  exact fillSlots trace maskLen frameLen gaps masked

/-- A stripped artifact's complete Function and Code vectors, read by the ordinary Core
vector parser. The reads start at their original count prefixes and end at their boundaries. -/
def DecodesAllFunctionVectors (source : Packed.Cursor) (funcs : List Func) : Prop :=
  ∃ spans ds dw cs cw,
    sectionSpans? source = some spans ∧ spans.lookup 3 = some (ds, dw) ∧
    spans.lookup 10 = some (cs, cw) ∧
    (readVec Core.Decode.readIdx) ⟨source.source.toByteArray, ds⟩ =
      .ok (funcs.map (·.type), ⟨source.source.toByteArray, ds + dw⟩) ∧
    (readVec readCode) ⟨source.source.toByteArray, cs⟩ =
      .ok (funcs.map functionCode, ⟨source.source.toByteArray, cs + cw⟩)

end SqliteWasmArtifact
