module

public import SqliteWasm.SectionRuns
public import SqliteWasm.Original
public import SqliteWasm.Object

public section

namespace SqliteWasm.MetadataEvidence

open SqliteWasm SqliteWasmArtifact
open Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Component.Chunked (runAll)
open Silmaril.Wasm.Component.ChunkedDecode

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

sqlite_check_eq typeLocation :
    ((sectionSpans? original).bind fun spans => spans.lookup 1) = some (11, 518)
sqlite_check_eq typeId : sectionBytes originalBytes 8 9 = [1]
sqlite_check_eq typeSize : runAll (readU 32) (sectionBytes originalBytes 9 11) = some 518
sqlite_check_eq types : runAll (readVec readRecType) (sectionBytes originalBytes 11 529) =
    some sqlite.types

theorem typeSection : SectionRun original 1 8 11 518 (fun s => { s with types := sqlite.types }) :=
  sectionRun_of_vec (source := original) (id := 1) (header := 8) (start := 11) (size := 518)
    (entries := sqlite.types) frame_readRecType body_types typeLocation (by decide)
    (by change 11 + 518 ≤ originalBytes.len; rw [originalBytes.len_eq]; decide)
    (by decide) typeId typeSize types

sqlite_check_eq importLocation :
    ((sectionSpans? original).bind fun spans => spans.lookup 2) = some (532, 918)
sqlite_check_eq importId : sectionBytes originalBytes 529 530 = [2]
sqlite_check_eq importSize : runAll (readU 32) (sectionBytes originalBytes 530 532) = some 918
sqlite_check_eq imports : runAll (readVec readImport) (sectionBytes originalBytes 532 1450) =
    some sqlite.imports

theorem importSection : SectionRun original 2 529 532 918 (fun s => { s with imports := sqlite.imports }) :=
  sectionRun_of_vec (source := original) (id := 2) (header := 529) (start := 532) (size := 918)
    (entries := sqlite.imports) frame_readImport body_imports importLocation (by decide)
    (by change 532 + 918 ≤ originalBytes.len; rw [originalBytes.len_eq]; decide)
    (by decide) importId importSize imports

sqlite_check_eq exportLocation :
    ((sectionSpans? original).bind fun spans => spans.lookup 7) = some (3020, 180)
sqlite_check_eq exportId : sectionBytes originalBytes 3017 3018 = [7]
sqlite_check_eq exportSize : runAll (readU 32) (sectionBytes originalBytes 3018 3020) = some 180
sqlite_check_eq exports : runAll (readVec readExport) (sectionBytes originalBytes 3020 3200) =
    some sqlite.exports

theorem exportSection : SectionRun original 7 3017 3020 180 (fun s => { s with exports := sqlite.exports }) :=
  sectionRun_of_vec (source := original) (id := 7) (header := 3017) (start := 3020) (size := 180)
    (entries := sqlite.exports) frame_readExport body_exports exportLocation (by decide)
    (by change 3020 + 180 ≤ originalBytes.len; rw [originalBytes.len_eq]; decide)
    (by decide) exportId exportSize exports

end SqliteWasm.MetadataEvidence
