module

import SqliteWasm.FunctionVectorCheck

open SqliteWasm SqliteWasmArtifact
open Silmaril.Wasm.Binary.Core.Decode (readU)
open Silmaril.Wasm.Component.Chunked (runAll)

example : DecodesFunctionVectors original reactorCodeCoverage sqlite.funcs :=
  originalFunctionVectors

example : sqlite.funcs.length = 1533 := quotedFunctionCount

example : (reactorCodeCoverage.filter id).length = 1529 := reactorCheckedBodyCount

example :
    reactorCodeCoverage.zipIdx.filterMap (fun entry => if entry.1 then none else some entry.2) =
      [99, 260, 719, 767] :=
  reactorFramingOnlyOrdinals

example :
    sectionSpans? original =
      some [(1, 11, 518), (2, 532, 918), (3, 1453, 1535), (4, 2990, 7), (5, 2999, 3),
        (6, 3004, 13), (7, 3020, 180), (9, 3203, 677), (10, 3884, 679518), (11, 683406, 58311)] :=
  originalSpans

example : runAll (readU 32) (bytesBetween originalBytes 1453 1455) = some 1533 :=
  originalDeclCount

example : runAll (readU 32) (bytesBetween originalBytes 3884 3886) = some 1533 :=
  originalCodeCount
