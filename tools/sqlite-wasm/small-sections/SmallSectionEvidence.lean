module

public import SqliteWasm.SectionRuns
public import SqliteWasm.Original
public import SqliteWasm.Object

public section

namespace SqliteWasm.SmallSectionEvidence

open SqliteWasm SqliteWasmArtifact
open Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Component.Chunked (runAll)
open Silmaril.Wasm.Component.ChunkedDecode

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

sqlite_check_eq tableLocation :
    ((sectionSpans? original).bind fun spans => spans.lookup 4) = some (2990, 7)
sqlite_check_eq tableId : sectionBytes originalBytes 2988 2989 = [4]
sqlite_check_eq tableSize : runAll (readU 32) (sectionBytes originalBytes 2989 2990) = some 7
sqlite_check_eq tables : runAll (readVec readTable) (sectionBytes originalBytes 2990 2997) =
    some sqlite.tables

theorem tableSection : SectionRun original 4 2988 2990 7 (fun s => { s with tables := sqlite.tables }) :=
  sectionRun_of_vec (source := original) (id := 4) (header := 2988) (start := 2990) (size := 7)
    (entries := sqlite.tables) frame_readTable body_tables tableLocation (by decide)
    (by change 2990 + 7 ≤ originalBytes.len; rw [originalBytes.len_eq]; decide)
    (by decide) tableId tableSize tables

sqlite_check_eq memoryLocation :
    ((sectionSpans? original).bind fun spans => spans.lookup 5) = some (2999, 3)
sqlite_check_eq memoryId : sectionBytes originalBytes 2997 2998 = [5]
sqlite_check_eq memorySize : runAll (readU 32) (sectionBytes originalBytes 2998 2999) = some 3
sqlite_check_eq memories : runAll (readVec readMemType) (sectionBytes originalBytes 2999 3002) =
    some sqlite.memories

theorem memorySection : SectionRun original 5 2997 2999 3 (fun s => { s with memories := sqlite.memories }) :=
  sectionRun_of_vec (source := original) (id := 5) (header := 2997) (start := 2999) (size := 3)
    (entries := sqlite.memories) frame_readMemType body_mems memoryLocation (by decide)
    (by change 2999 + 3 ≤ originalBytes.len; rw [originalBytes.len_eq]; decide)
    (by decide) memoryId memorySize memories

sqlite_check_eq globalLocation :
    ((sectionSpans? original).bind fun spans => spans.lookup 6) = some (3004, 13)
sqlite_check_eq globalId : sectionBytes originalBytes 3002 3003 = [6]
sqlite_check_eq globalSize : runAll (readU 32) (sectionBytes originalBytes 3003 3004) = some 13
sqlite_check_eq globals : runAll (readVec readGlobal) (sectionBytes originalBytes 3004 3017) =
    some sqlite.globals

theorem globalSection : SectionRun original 6 3002 3004 13 (fun s => { s with globals := sqlite.globals }) :=
  sectionRun_of_vec (source := original) (id := 6) (header := 3002) (start := 3004) (size := 13)
    (entries := sqlite.globals) frame_readGlobal body_globals globalLocation (by decide)
    (by change 3004 + 13 ≤ originalBytes.len; rw [originalBytes.len_eq]; decide)
    (by decide) globalId globalSize globals

sqlite_check_eq elementLocation :
    ((sectionSpans? original).bind fun spans => spans.lookup 9) = some (3203, 677)
sqlite_check_eq elementId : sectionBytes originalBytes 3200 3201 = [9]
sqlite_check_eq elementSize : runAll (readU 32) (sectionBytes originalBytes 3201 3203) = some 677
sqlite_check_eq elems : runAll (readVec readElem) (sectionBytes originalBytes 3203 3880) =
    some sqlite.elems

theorem elementSection : SectionRun original 9 3200 3203 677 (fun s => { s with elems := sqlite.elems }) :=
  sectionRun_of_vec (source := original) (id := 9) (header := 3200) (start := 3203) (size := 677)
    (entries := sqlite.elems) frame_readElem body_elems elementLocation (by decide)
    (by change 3203 + 677 ≤ originalBytes.len; rw [originalBytes.len_eq]; decide)
    (by decide) elementId elementSize elems

end SqliteWasm.SmallSectionEvidence
