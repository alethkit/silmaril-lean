module

public import SqliteWasm.Original
public import SqliteWasm.Object
public import Silmaril.Wasm.Binary.Core.Decode
import SqliteWasm.AllFunctionVectors
import SqliteWasm.MetadataVectors
import SqliteWasm.SmallSections
import SqliteWasm.DataSection
import SqliteWasm.DataIndices

namespace SqliteWasm.WholeModuleEvidence

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary SqliteWasmArtifact
open Core.Decode
open Silmaril.Wasm.Component.Chunked (arr runAll)
open Silmaril.Wasm.Component.ChunkedDecode

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem fileLength : originalBytes.toList.length = 741717 :=
  (originalBytes.length_toList originalBytes.wf_true).trans originalBytes.len_eq

private theorem fileBound {n : Nat} (h : n ≤ 741717) : n ≤ originalBytes.len :=
  originalBytes.len_eq.symm ▸ h

sqlite_check_eq headerSlice : sectionBytes originalBytes 0 8 = magic ++ version

private theorem header : originalBytes.toList.take 8 = magic ++ version := by
  have checked := headerSlice
  simpa only [sectionBytes, Nat.sub_zero, originalBytes.toList_slice 0 8 originalBytes.wf_true
    (fileBound (by decide)), List.drop_zero] using checked

sqlite_check_eq sectionLayout :
    sectionSpans? original = some [
      (1, 11, 518), (2, 532, 918), (3, 1453, 1535), (4, 2990, 7), (5, 2999, 3),
      (6, 3004, 13), (7, 3020, 180), (9, 3203, 677), (10, 3884, 679518),
      (11, 683406, 58311)]

sqlite_check_eq functionId : sectionBytes originalBytes 1450 1451 = [3]
sqlite_check_eq functionSize :
    runAll (readU 32) (sectionBytes originalBytes 1451 1453) = some 1535
sqlite_check_eq codeId : sectionBytes originalBytes 3880 3881 = [10]
sqlite_check_eq codeSize :
    runAll (readU 32) (sectionBytes originalBytes 3881 3884) = some 679518

private theorem vectorsAt :
    readVec (readIdx (k := .type_)) ⟨originalBytes.toByteArray, 1453⟩ =
      .ok (sqlite.funcs.map Func.type, ⟨originalBytes.toByteArray, 2988⟩) ∧
    readVec readCode ⟨originalBytes.toByteArray, 3884⟩ =
      .ok (sqlite.funcs.map functionCode, ⟨originalBytes.toByteArray, 683402⟩) := by
  obtain ⟨spans, fs, fw, cs, cw, scan, functionAt, codeAt, types, codes⟩ :=
    originalAllFunctionVectors
  rw [sectionLayout] at scan
  cases Option.some.inj scan
  change some (1453, 1535) = some (fs, fw) at functionAt
  change some (3884, 679518) = some (cs, cw) at codeAt
  simp only [Option.some.injEq, Prod.mk.injEq] at functionAt codeAt
  obtain ⟨rfl, rfl⟩ := functionAt
  obtain ⟨rfl, rfl⟩ := codeAt
  exact ⟨types, codes⟩

private theorem functionSection : SectionRun original 3 1450 1453 1535
    (fun s => { s with funcTypes := sqlite.funcs.map Func.type }) :=
  sectionRun_of_readVec (source := original) (id := 3) (header := 1450) (start := 1453)
    (size := 1535) body_funcs (by rw [sectionLayout]; rfl) (by decide) (fileBound (by decide))
    (by decide) functionId functionSize vectorsAt.1

private theorem codeSection : SectionRun original 10 3880 3884 679518
    (fun s => { s with code := sqlite.funcs.map functionCode }) :=
  sectionRun_of_readVec (source := original) (id := 10) (header := 3880) (start := 3884)
    (size := 679518) body_code (by rw [sectionLayout]; rfl) (by decide) (fileBound (by decide))
    (by decide) codeId codeSize vectorsAt.2

private def finalSections : Sections where
  types := sqlite.types
  imports := sqlite.imports
  funcTypes := sqlite.funcs.map Func.type
  tables := sqlite.tables
  memories := sqlite.memories
  tags := []
  globals := sqlite.globals
  exports := sqlite.exports
  start := none
  elems := sqlite.elems
  dataCount := none
  code := sqlite.funcs.map functionCode
  data := sqlite.data

/-- Ten section steps, followed by the ordinary EOF branch with fuel remaining. -/
private theorem sectionLoop (fuel : Nat) :
    readModule.go (fuel + 11) 0 {} ⟨originalBytes.toByteArray, 8⟩ =
      .ok (finalSections, ⟨originalBytes.toByteArray, 741717⟩) := by
  refine (originalTypeSection.step (fuel + 10) 0 {} (by decide)).trans ?_
  refine (originalImportSection.step (fuel + 9) 1 _ (by decide)).trans ?_
  refine (functionSection.step (fuel + 8) 2 _ (by decide)).trans ?_
  refine (originalTableSection.step (fuel + 7) 3 _ (by decide)).trans ?_
  refine (originalMemorySection.step (fuel + 6) 4 _ (by decide)).trans ?_
  refine (originalGlobalSection.step (fuel + 5) 5 _ (by decide)).trans ?_
  refine (originalExportSection.step (fuel + 4) 7 _ (by decide)).trans ?_
  refine (originalElementSection.step (fuel + 3) 8 _ (by decide)).trans ?_
  refine (codeSection.step (fuel + 2) 10 _ (by decide)).trans ?_
  refine (originalDataSection.step (fuel + 1) 12 _ (by decide)).trans ?_
  have stop := go_end (B := originalBytes.toList) (fuel := fuel) (last := 13) (S := finalSections)
  rwa [fileLength] at stop

private theorem zipProjected (funcs : List Func) :
    Core.zipFuncs (funcs.map Func.type) (funcs.map functionCode) = funcs := by
  induction funcs with
  | nil => rfl
  | cons f fs ih =>
    change f :: Core.zipFuncs (fs.map Func.type) (fs.map functionCode) = f :: fs
    rw [ih]

private theorem assemble (m : Wasm.Module) (tags : m.tags = []) (start : m.start = none) :
    ({
      types := m.types
      imports := m.imports
      tags := []
      globals := m.globals
      tables := m.tables
      memories := m.memories
      elems := m.elems
      funcs := Core.zipFuncs (m.funcs.map Func.type) (m.funcs.map functionCode)
      data := m.data
      start := none
      exports := m.exports } : Wasm.Module) = m := by
  rw [zipProjected, ← tags, ← start]

public theorem originalDecode : Core.decode? originalBytes.toByteArray = some sqlite := by
  have loop : readModule.go originalBytes.toList.length 0 {} ⟨arr originalBytes.toList, 8⟩ =
      .ok (finalSections, ⟨arr originalBytes.toList, originalBytes.toList.length⟩) := by
    rw [fileLength]
    exact sectionLoop 741706
  have counts : finalSections.funcTypes.length = finalSections.code.length := by
    change (sqlite.funcs.map Func.type).length = (sqlite.funcs.map functionCode).length
    simp only [List.length_map]
  have decoded := decode_of_go header (fileLength.symm ▸ (by decide : 8 ≤ 741717))
    loop counts rfl quotedCodeIndicesEmpty
  exact decoded.trans (congrArg some (assemble sqlite rfl rfl))

end SqliteWasm.WholeModuleEvidence
