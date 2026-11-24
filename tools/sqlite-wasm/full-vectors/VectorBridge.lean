module

public import SqliteWasm.CodeCoverage
public import SqliteWasm.Object
public import SqliteWasm.Original
import SqliteWasm.CodeFrames
import SqliteWasm.FunctionVectorCheck
import SqliteWasm.LargeBodies

public section

namespace SqliteWasm.VectorBridge

open SqliteWasm SqliteWasmArtifact Silmaril.Wasm
open Silmaril.Wasm.Binary.Core.Decode (readCode readU)
open Silmaril.Wasm.Component.Chunked (runAll)

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

sqlite_check_eq reactorMaskLength : reactorCodeCoverage.length = 1533
sqlite_check_eq reactorFrameLength : reactorCodeCoverage.length = originalBodyFrames.length

sqlite_check_eq frame99 : originalBodyFrames[99]? = some (38354, 76747)
sqlite_check_eq frame260 : originalBodyFrames[260]? = some (134349, 148373)
sqlite_check_eq frame719 : originalBodyFrames[719]? = some (311161, 325196)
sqlite_check_eq frame767 : originalBodyFrames[767]? = some (348781, 364946)

sqlite_check_eq location99 : codeFrameAt? original 99 = some (38354, 76747)
sqlite_check_eq location260 : codeFrameAt? original 260 = some (134349, 148373)
sqlite_check_eq location719 : codeFrameAt? original 719 = some (311161, 325196)
sqlite_check_eq location767 : codeFrameAt? original 767 = some (348781, 364946)

private theorem gapRun {i start stop : Nat} {f : Func}
    (picked : sqlite.funcs[i]? = some f)
    (location : codeFrameAt? original i = some (start, stop))
    (whole : ReadsCodeAt original i (sqlite.funcs.map functionCode)[i]!) :
    readCode ⟨originalBytes.toByteArray, start⟩ =
      .ok (functionCode f, ⟨originalBytes.toByteArray, stop⟩) := by
  obtain ⟨a, b, found, run⟩ := whole
  rw [location] at found
  cases found
  have pickedCode : (sqlite.funcs.map functionCode)[i]? = some (functionCode f) := by
    rw [List.getElem?_map, picked]
    rfl
  rwa [List.getElem!_of_getElem? pickedCode] at run

private theorem allGapRuns : GapReads originalBytes.toByteArray reactorCodeCoverage
    sqlite.funcs originalBodyFrames := by
  intro i f start stop uncovered picked frame
  have missing : i ∈ reactorCodeCoverage.zipIdx.filterMap
      (fun entry => if entry.1 then none else some entry.2) :=
    List.mem_filterMap.mpr ⟨(false, i), List.mk_mem_zipIdx_iff_getElem?.mpr uncovered, rfl⟩
  rw [reactorFramingOnlyOrdinals] at missing
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at missing
  rcases missing with rfl | rfl | rfl | rfl
  · rw [frame99] at frame
    cases frame
    exact gapRun picked location99 originalCode99
  · rw [frame260] at frame
    cases frame
    exact gapRun picked location260 originalCode260
  · rw [frame719] at frame
    cases frame
    exact gapRun picked location719 originalCode719
  · rw [frame767] at frame
    cases frame
    exact gapRun picked location767 originalCode767

/-- The original reactor's complete Function and Code vectors agree with every defined
function in the quotation, in order, including each expanded locals vector and body. -/
theorem originalAllFunctionVectors : DecodesAllFunctionVectors original sqlite.funcs := by
  obtain ⟨length, spans, ds, dw, cs, cw, layout, declAt, codeAt, decls, masked⟩ := originalFunctionVectors
  refine ⟨spans, ds, dw, cs, cw, layout, declAt, codeAt, decls, ?_⟩
  have sameLayout := Option.some.inj (layout.symm.trans originalSpans)
  rw [sameLayout] at codeAt
  have code : (cs, cw) = (3884, 679518) := (Option.some.inj codeAt).symm
  have codeStart := congrArg Prod.fst code
  have codeWidth := congrArg Prod.snd code
  change cs = 3884 at codeStart
  change cw = 679518 at codeWidth
  subst cs
  subst cw
  have count : runAll (readU 32) (bytesBetween originalBytes 3884 3886) =
      some reactorCodeCoverage.length := by
    rw [reactorMaskLength]
    exact originalCodeCount
  exact readFullCodeVector (source := originalBytes) (entries := 3886)
    originalBytes.wf_true (by decide) (by rw [reactorMaskLength, originalBytes.len_eq]; decide)
    count length reactorFrameLength originalFrameTrace allGapRuns masked

#print axioms originalAllFunctionVectors

end SqliteWasm.VectorBridge
