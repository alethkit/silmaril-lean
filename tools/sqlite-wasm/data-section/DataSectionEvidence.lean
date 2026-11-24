module

public import SqliteWasm.SectionRuns
public import SqliteWasm.Original
public import SqliteWasm.Object

namespace SqliteWasm.DataSectionEvidence

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary SqliteWasmArtifact
open Core.Decode
open Silmaril.Wasm.Component.Chunked (arr runAll)
open Silmaril.Wasm.Component.ChunkedDecode

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem countAt {source : KBytes} (wf : source.wf = true)
    {start stop count : Nat} (ordered : start ≤ stop) (fits : stop + count ≤ source.len)
    (countBytes : runAll (readU 32) (sectionBytes source start stop) = some count) :
    readCount ⟨source.toByteArray, start⟩ = .ok (count, ⟨source.toByteArray, stop⟩) := by
  have read := readSectionSlice wf ordered (by omega) (frame_readU 32) countBytes
  have atStop : start + (stop - start) = stop := by omega
  have checked := readCount_at (B := source.toList) (x := start) (k := stop - start) (n := count)
    (by rw [atStop]; exact read)
    (by rw [atStop, source.length_toList wf]; omega)
  rwa [atStop] at checked

/-- Compare packed windows, then use the library's extraction law for the ordinary reader. -/
private theorem payloadAt {source payload : KBytes} (wf : source.wf = true)
    (payloadWf : payload.wf = true) {start width : Nat} (fits : start + width ≤ source.len)
    (same : (source.slice start width).sameBytes 65536 payload = true) :
    readBytes width ⟨source.toByteArray, start⟩ =
      .ok (payload.toByteArray, ⟨source.toByteArray, start + width⟩) := by
  have bytes := KBytes.toList_eq_of_sameBytes 65536 _ _ (source.wf_slice _ _ wf fits) payloadWf same
  rw [source.toList_slice _ _ wf fits] at bytes
  have size : source.toByteArray.size = source.len := source.length_toList wf
  simp only [readBytes_apply, size, fits, ↓reduceIte]
  change Except.ok ((arr source.toList).extract start (start + width), _) = _
  rw [extract_arr, bytes]
  rfl

private theorem activeAt {bytes payload : ByteArray} {start exprStart lengthStart payloadStart width stop : Nat}
    {offset : Wasm.Expr}
    (mode : readU 32 ⟨bytes, start⟩ = .ok (0, ⟨bytes, exprStart⟩))
    (expr : readExpr ⟨bytes, exprStart⟩ = .ok (offset, ⟨bytes, lengthStart⟩))
    (length : readCount ⟨bytes, lengthStart⟩ = .ok (width, ⟨bytes, payloadStart⟩))
    (body : readBytes width ⟨bytes, payloadStart⟩ = .ok (payload, ⟨bytes, stop⟩)) :
    readData ⟨bytes, start⟩ = .ok (⟨payload, .active ⟨0⟩ offset⟩, ⟨bytes, stop⟩) := by
  unfold readData
  rw [bind_ok mode]
  simp only
  rw [bind_ok expr]
  unfold readData.readByteVec
  rw [bind_apply, bind_ok length, body]
  rfl

kbytes_def payload0 from_file "DataPayload0.bin"
kbytes_def payload1 from_file "DataPayload1.bin"

sqlite_check_eq mode0 : runAll (readU 32) (sectionBytes originalBytes 683407 683408) = some 0
sqlite_check_eq expr0 : runAll readExpr (sectionBytes originalBytes 683408 683412) = some [.intConst .i32 1024]
sqlite_check_eq length0 : runAll (readU 32) (sectionBytes originalBytes 683412 683415) = some 51370
sqlite_check_eq bytes0 : (originalBytes.slice 683415 51370).sameBytes 65536 payload0 = true

sqlite_check_eq mode1 : runAll (readU 32) (sectionBytes originalBytes 734785 734786) = some 0
sqlite_check_eq expr1 : runAll readExpr (sectionBytes originalBytes 734786 734791) = some [.intConst .i32 52400]
sqlite_check_eq length1 : runAll (readU 32) (sectionBytes originalBytes 734791 734793) = some 6924
sqlite_check_eq bytes1 : (originalBytes.slice 734793 6924).sameBytes 65536 payload1 = true

private theorem quotedData : sqlite.data =
    [⟨payload0.toByteArray, .active ⟨0⟩ [.intConst .i32 1024]⟩,
     ⟨payload1.toByteArray, .active ⟨0⟩ [.intConst .i32 52400]⟩] := rfl

private theorem originalBound {n : Nat} (h : n ≤ 741717) : n ≤ originalBytes.len :=
  originalBytes.len_eq.symm ▸ h

private theorem segment0 : readData ⟨originalBytes.toByteArray, 683407⟩ =
    .ok (⟨payload0.toByteArray, .active ⟨0⟩ [.intConst .i32 1024]⟩, ⟨originalBytes.toByteArray, 734785⟩) :=
  activeAt
    (readSectionSlice originalBytes.wf_true (by decide) (originalBound (by decide)) (frame_readU 32) mode0)
    (readSectionSlice originalBytes.wf_true (by decide) (originalBound (by decide)) frame_readExpr expr0)
    (countAt originalBytes.wf_true (by decide) (originalBound (by decide)) length0)
    (payloadAt originalBytes.wf_true payload0.wf_true (originalBound (by decide)) bytes0)

private theorem segment1 : readData ⟨originalBytes.toByteArray, 734785⟩ =
    .ok (⟨payload1.toByteArray, .active ⟨0⟩ [.intConst .i32 52400]⟩, ⟨originalBytes.toByteArray, 741717⟩) :=
  activeAt
    (readSectionSlice originalBytes.wf_true (by decide) (originalBound (by decide)) (frame_readU 32) mode1)
    (readSectionSlice originalBytes.wf_true (by decide) (originalBound (by decide)) frame_readExpr expr1)
    (countAt originalBytes.wf_true (by decide) (originalBound (by decide)) length1)
    (payloadAt originalBytes.wf_true payload1.wf_true (originalBound (by decide)) bytes1)

sqlite_check_eq segmentCount : runAll (readU 32) (sectionBytes originalBytes 683406 683407) = some 2
sqlite_check_eq location : ((sectionSpans? original).bind fun spans => spans.lookup 11) = some (683406, 58311)
sqlite_check_eq identifier : sectionBytes originalBytes 683402 683403 = [11]
sqlite_check_eq sizePrefix : runAll (readU 32) (sectionBytes originalBytes 683403 683406) = some 58311

private theorem vector : readVec readData ⟨originalBytes.toByteArray, 683406⟩ =
    .ok (sqlite.data, ⟨originalBytes.toByteArray, 741717⟩) := by
  have tail : readVec.go readData 1 ⟨originalBytes.toByteArray, 734785⟩ =
      .ok ([⟨payload1.toByteArray, .active ⟨0⟩ [.intConst .i32 52400]⟩],
        ⟨originalBytes.toByteArray, 741717⟩) := by
    rw [readVec_go_succ, bind_ok segment1]
    rfl
  unfold readVec
  rw [bind_ok (countAt originalBytes.wf_true (by decide) (originalBound (by decide)) segmentCount),
    readVec_go_succ, bind_ok segment0, bind_ok tail, quotedData]
  rfl

public theorem dataSection : SectionRun original 11 683402 683406 58311 (fun s => { s with data := sqlite.data }) :=
  sectionRun_of_readVec (source := original) (id := 11) (header := 683402) (start := 683406)
    (size := 58311) body_data location (by decide) (originalBound (by decide))
    (by decide) identifier sizePrefix vector

end SqliteWasm.DataSectionEvidence
