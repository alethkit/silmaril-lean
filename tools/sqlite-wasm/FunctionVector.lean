module

public import SqliteWasmArtifactEntries
public import Silmaril.Wasm.Component.ChunkedDecode.Thms

@[expose] public section

namespace SqliteWasmArtifact

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary
open Core.Decode (DecodeM readCode readIdx readU readVec readBytes readCount decodeError)
open Silmaril.Wasm.Component.Chunked (CPlan arr runAll chkSeq chkCode)
open Silmaril.Wasm.Component.ChunkedDecode

abbrev CodeEntry := List ValType × Wasm.Expr

/-- The original interval `[start, stop)`, kept packed until this interval is checked. -/
def bytesBetween (source : KBytes) (start stop : Nat) : List UInt8 :=
  (source.slice start (stop - start)).toList

/-- A skipped body's size prefix is still read and its full byte range is consumed. -/
def readCodeSlot (check : Bool) : DecodeM (Option CodeEntry) :=
  if check then some <$> readCode else do
    let size ← readU 32
    let _ ← readBytes size
    return none

def readCodeSlots : List Bool → DecodeM (List (Option CodeEntry))
  | [] => pure []
  | check :: tail => do
    let body ← readCodeSlot check
    let rest ← readCodeSlots tail
    return body :: rest

def readCodeVector (mask : List Bool) : DecodeM (List (Option CodeEntry)) := do
  let count ← readCount
  unless count = mask.length do decodeError "code count differs from coverage length"
  readCodeSlots mask

/-- One position per defined function, including `none` for bodies checked only for framing. -/
def projectCode (mask : List Bool) (funcs : List Func) : List (Option CodeEntry) :=
  List.zipWith (fun check f => if check then some (f.locals, f.body) else none) mask funcs

private theorem projectCode_mask {mask : List Bool} {funcs : List Func}
    (length : mask.length = funcs.length) : (projectCode mask funcs).map Option.isSome = mask := by
  induction mask generalizing funcs with
  | nil => rfl
  | cons check tail ih =>
    cases funcs with
    | nil => simp at length
    | cons f rest =>
      have same : tail.length = rest.length := Nat.succ.inj length
      cases check <;> exact congrArg (List.cons _) (ih same)

/-- The original header and envelopes identify the two vectors. The Core reader decodes
all declarations. The masked Code reader decodes the covered bodies with the Core reader and
checks only size framing for the other slots. Both vectors end at their declared boundaries. -/
def DecodesFunctionVectors (source : Packed.Cursor) (mask : List Bool) (funcs : List Func) : Prop :=
  mask.length = funcs.length ∧
  ∃ spans ds dw cs cw,
    sectionSpans? source = some spans ∧ spans.lookup 3 = some (ds, dw) ∧
    spans.lookup 10 = some (cs, cw) ∧
    (readVec readIdx) ⟨source.source.toByteArray, ds⟩ =
      .ok (funcs.map (·.type), ⟨source.source.toByteArray, ds + dw⟩) ∧
    (readCodeVector mask) ⟨source.source.toByteArray, cs⟩ =
      .ok (projectCode mask funcs, ⟨source.source.toByteArray, cs + cw⟩)

inductive CodePlan where
  | direct
  | split (plan : CPlan)
  | skip (sizeWidth : Nat)
  deriving Inhabited

def readPlannedBody (plan : CPlan) (bytes : List UInt8) : Option CodeEntry :=
  if chkLocals [plan] bytes then
    match chkCode plan bytes with
    | some (code, []) => some code
    | _ => none
  else none

/-- An outer `none` rejects the plan. `some none` certifies only the framed size. -/
def checkCodeSlot (source : KBytes) (start stop : Nat) (plan : CodePlan) : Option (Option CodeEntry) :=
  match plan with
  | .direct => (runAll readCode (bytesBetween source start stop)).map some
  | .split plan => (readPlannedBody plan (bytesBetween source start stop)).map some
  | .skip width => do
    if start + width ≤ stop then
      let size ← runAll (readU 32) (bytesBetween source start (start + width))
      if start + width + size = stop then some none else none
    else none

/-- The proposed cuts must be increasing and cover the entire block. -/
def checkCodeBlock (source : KBytes) (stop : Nat) :
    List (Nat × CodePlan) → Nat → Option (List (Option CodeEntry))
  | [], pos => if pos = stop then some [] else none
  | (cut, plan) :: cuts, pos => do
    if pos < cut ∧ cut ≤ stop then
      let code ← checkCodeSlot source pos cut plan
      let rest ← checkCodeBlock source stop cuts cut
      return code :: rest
    else none

theorem checkCodeBlock_cons {source : KBytes} {start cut stop : Nat} {plan : CodePlan}
    {cuts : List (Nat × CodePlan)} {code : Option CodeEntry} {rest : List (Option CodeEntry)}
    (ordered : start < cut ∧ cut ≤ stop) (entry : checkCodeSlot source start cut plan = some code)
    (tail : checkCodeBlock source stop cuts cut = some rest) :
    checkCodeBlock source stop ((cut, plan) :: cuts) start = some (code :: rest) := by
  simp [checkCodeBlock, ordered, entry, tail]

/-- The two consecutive runs that contribute the same block of defined-function slots. -/
def FunctionBlock (source : KBytes) (declStart declStop codeStart codeStop : Nat)
    (mask : List Bool) (funcs : List Func) : Prop :=
  mask.length = funcs.length ∧
  VecSeg readIdx source.toList declStart declStop (funcs.map (·.type)) ∧
  (readCodeSlots mask) ⟨source.toByteArray, codeStart⟩ =
    .ok (projectCode mask funcs, ⟨source.toByteArray, codeStop⟩)

private theorem readCodeSlots_append {source : ByteArray} {start middle stop : Nat}
    {ms ns : List Bool} {xs ys : List (Option CodeEntry)}
    (left : (readCodeSlots ms) ⟨source, start⟩ = .ok (xs, ⟨source, middle⟩))
    (right : (readCodeSlots ns) ⟨source, middle⟩ = .ok (ys, ⟨source, stop⟩)) :
    (readCodeSlots (ms ++ ns)) ⟨source, start⟩ = .ok (xs ++ ys, ⟨source, stop⟩) := by
  have step : ∀ masks, readCodeSlots (masks ++ ns) = (do
      let first ← readCodeSlots masks
      let last ← readCodeSlots ns
      pure (first ++ last)) := by
    intro masks
    induction masks with
    | nil => simp [readCodeSlots]
    | cons flag rest ih => simp [readCodeSlots, ih, bind_assoc]
  rw [step, bind_ok left, bind_ok right]
  rfl

theorem FunctionBlock.append {source : KBytes} {ds dm de cs cm ce : Nat}
    {ms ns : List Bool} {fs gs : List Func}
    (left : FunctionBlock source ds dm cs cm ms fs) (right : FunctionBlock source dm de cm ce ns gs) :
    FunctionBlock source ds de cs ce (ms ++ ns) (fs ++ gs) := by
  refine ⟨by simp only [List.length_append, left.1, right.1], ?_, ?_⟩
  · rw [List.map_append]
    exact left.2.1.append right.2.1
  · unfold projectCode
    rw [List.zipWith_append left.1]
    exact readCodeSlots_append left.2.2 right.2.2

theorem FunctionBlock.nil {source : KBytes} {decl code : Nat} :
    FunctionBlock source decl decl code code [] [] := ⟨rfl, VecSeg.nil, rfl⟩

private theorem bytesAt {source : KBytes} (wf : source.wf = true) {start stop : Nat}
    (ordered : start ≤ stop) (bound : stop ≤ source.len) :
    At source.toList start (bytesBetween source start stop) ∧
      (bytesBetween source start stop).length = stop - start := by
  have fit : start + (stop - start) ≤ source.len := by omega
  have len := (source.slice start (stop - start)).length_toList (source.wf_slice _ _ wf fit)
  rw [source.len_slice] at len
  change (bytesBetween source start stop).length = stop - start at len
  refine ⟨⟨?_, ?_⟩, len⟩
  · rw [len]
    exact (source.toList_slice _ _ wf fit).symm
  · rw [len, source.length_toList wf]
    omega

private theorem readPlannedBody_sound {bytes source : List UInt8} {start : Nat}
    {plan : CPlan} {code : CodeEntry} (checked : readPlannedBody plan bytes = some code)
    (atStart : At source start bytes) :
    readCode ⟨arr source, start⟩ = .ok (code, ⟨arr source, start + bytes.length⟩) := by
  simp only [readPlannedBody] at checked
  split at checked
  · rename_i locals
    split at checked
    · rename_i entry parsed
      cases checked
      have cap := chkCode_locals parsed
      obtain ⟨len, groups, sizeAt, _, localsAt, localsEq⟩ := cap
      simp only [chkLocals, sizeAt, localsAt, Bool.and_true, decide_eq_true_eq] at locals
      have hcap : code.1.length ≤ Core.Decode.maxLocals := by rw [localsEq]; exact locals
      obtain ⟨consumed, eq, run⟩ := readCode_of_chkCode parsed atStart hcap
      rw [List.append_nil] at eq
      rwa [← eq] at run
    · cases checked
  · cases checked

private theorem checkCodeSlot_sound {source : KBytes} (wf : source.wf = true) {start stop : Nat}
    (ordered : start ≤ stop) (bound : stop ≤ source.len) {plan : CodePlan} {slot : Option CodeEntry}
    (checked : checkCodeSlot source start stop plan = some slot) :
    (readCodeSlot slot.isSome) ⟨source.toByteArray, start⟩ =
      .ok (slot, ⟨source.toByteArray, stop⟩) := by
  cases plan with
  | direct | split plan =>
    simp only [checkCodeSlot] at checked
    obtain ⟨code, decoded, rfl⟩ := Option.map_eq_some_iff.1 checked
    have slice := bytesAt wf ordered bound
    have run := by
      first
      | exact run_of_runAll frame_readCode decoded slice.1
      | exact readPlannedBody_sound decoded slice.1
    rw [slice.2, show start + (stop - start) = stop by omega] at run
    change readCode ⟨source.toByteArray, start⟩ =
      .ok (code, ⟨source.toByteArray, stop⟩) at run
    simp only [Option.isSome_some, readCodeSlot, ↓reduceIte]
    change (fun p : CodeEntry × Core.Decode.Cursor => (some p.1, p.2)) <$>
      readCode ⟨source.toByteArray, start⟩ = _
    rw [run]
    rfl
  | skip width =>
    simp only [checkCodeSlot] at checked
    split at checked
    · rename_i widthFits
      obtain ⟨size, sizeAt, eq⟩ := Option.bind_eq_some_iff.1 checked
      split at eq
      · rename_i endPos
        cases eq
        have slice := bytesAt wf (Nat.le_add_right start width) (Nat.le_trans widthFits bound)
        have run := run_of_runAll (frame_readU 32) sizeAt slice.1
        rw [slice.2, show start + width - start = width by omega] at run
        change readU 32 ⟨source.toByteArray, start⟩ =
          .ok (size, ⟨source.toByteArray, start + width⟩) at run
        simp only [Option.isSome_none, readCodeSlot, Bool.false_eq_true, ↓reduceIte]
        rw [bind_ok run, bind_apply, readBytes_apply]
        have sizeEq : source.toByteArray.size = source.len := source.length_toList wf
        simp only [sizeEq, endPos, bound]
        rfl
      · cases eq
    · cases checked

private theorem checkCodeBlock_sound {source : KBytes} (wf : source.wf = true) {stop : Nat}
    (bound : stop ≤ source.len) {cuts : List (Nat × CodePlan)} {start : Nat}
    {codes : List (Option CodeEntry)} (checked : checkCodeBlock source stop cuts start = some codes) :
    (readCodeSlots (codes.map Option.isSome)) ⟨source.toByteArray, start⟩ =
      .ok (codes, ⟨source.toByteArray, stop⟩) := by
  induction cuts generalizing start codes with
  | nil =>
    simp only [checkCodeBlock] at checked
    split at checked
    · rename_i atStop
      cases checked
      subst start
      rfl
    · cases checked
  | cons entry cuts ih =>
    obtain ⟨cut, plan⟩ := entry
    simp only [checkCodeBlock] at checked
    split at checked
    · rename_i ordered
      obtain ⟨code, codeAt, more⟩ := Option.bind_eq_some_iff.1 checked
      obtain ⟨rest, restAt, eq⟩ := Option.bind_eq_some_iff.1 more
      cases eq
      have first := checkCodeSlot_sound wf (Nat.le_of_lt ordered.1) (Nat.le_trans ordered.2 bound) codeAt
      simp only [List.map_cons, readCodeSlots]
      rw [bind_ok first, bind_ok (ih restAt)]
      rfl
    · cases checked

/-- A declaration slice and independent code records certify a block of quoted functions. -/
theorem functionBlock_of_checks {source : KBytes} (wf : source.wf = true)
    {ds de cs ce : Nat} {cuts : List (Nat × CodePlan)} {mask : List Bool} {fs : List Func}
    (declOrder : ds ≤ de) (declBound : de ≤ source.len) (codeBound : ce ≤ source.len)
    (length : mask.length = fs.length)
    (decls : chkSeq readIdx [de - ds] (bytesBetween source ds de) = some (fs.map (·.type), []))
    (codes : checkCodeBlock source ce cuts cs = some (projectCode mask fs)) :
    FunctionBlock source ds de cs ce mask fs := by
  have slice := bytesAt wf declOrder declBound
  have run := vecSeg_of_chkSeq frame_readIdx decls slice.1
  rw [slice.2, show ds + (de - ds) = de by omega] at run
  have codeRun := checkCodeBlock_sound wf codeBound codes
  rw [projectCode_mask length] at codeRun
  exact ⟨length, run, codeRun⟩

private theorem readCount_of_prefix {source : KBytes} (wf : source.wf = true)
    {start entries count : Nat} (ordered : start ≤ entries) (bound : entries + count ≤ source.len)
    (countPrefix : runAll (readU 32) (bytesBetween source start entries) = some count) :
    readCount ⟨source.toByteArray, start⟩ = .ok (count, ⟨source.toByteArray, entries⟩) := by
  have slice := bytesAt wf ordered (by omega : entries ≤ source.len)
  have run := run_of_runAll (frame_readU 32) countPrefix slice.1
  rw [slice.2] at run
  have countRun := readCount_at run (by rw [source.length_toList wf]; omega)
  rwa [show start + (entries - start) = entries by omega] at countRun

/-- Close the declaration vector using its original count and consecutive entry runs. -/
theorem readDeclVector_of_block {source : KBytes} (wf : source.wf = true)
    {start entries stop count : Nat} {values : List TypeIdx}
    (ordered : start ≤ entries) (bound : entries + count ≤ source.len)
    (countPrefix : runAll (readU 32) (bytesBetween source start entries) = some count)
    (length : values.length = count) (block : VecSeg readIdx source.toList entries stop values) :
    (readVec readIdx) ⟨source.toByteArray, start⟩ = .ok (values, ⟨source.toByteArray, stop⟩) := by
  unfold readVec
  rw [bind_ok (readCount_of_prefix wf ordered bound countPrefix), ← length]
  change readVec.go readIdx values.length ⟨arr source.toList, entries⟩ = _
  simpa only [Nat.add_zero, List.append_nil] using block 0 [] ⟨source.toByteArray, stop⟩ rfl

/-- Close the masked code vector using its original count and consecutive slot runs. -/
theorem readCodeVector_of_block {source : KBytes} (wf : source.wf = true)
    {start entries stop count : Nat} {mask : List Bool} {values : List (Option CodeEntry)}
    (ordered : start ≤ entries) (bound : entries + count ≤ source.len)
    (countPrefix : runAll (readU 32) (bytesBetween source start entries) = some count)
    (length : mask.length = count)
    (block : (readCodeSlots mask) ⟨source.toByteArray, entries⟩ =
      .ok (values, ⟨source.toByteArray, stop⟩)) :
    (readCodeVector mask) ⟨source.toByteArray, start⟩ =
      .ok (values, ⟨source.toByteArray, stop⟩) := by
  unfold readCodeVector
  rw [bind_ok (readCount_of_prefix wf ordered bound countPrefix)]
  simpa [length] using block

end SqliteWasmArtifact
