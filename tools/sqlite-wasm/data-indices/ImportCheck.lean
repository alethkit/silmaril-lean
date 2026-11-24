module

import SqliteWasm.DataIndices
import SqliteWasm.AllFunctionVectors

open SqliteWasm SqliteWasmArtifact Silmaril.Wasm.Binary
open Core.Decode (readVec readCode)

example : Core.codesDataIdxs (sqlite.funcs.map functionCode) = [] := quotedCodeIndicesEmpty

example : ∃ (start size : Nat) (codes : List CodeEntry),
    readVec readCode ⟨originalBytes.toByteArray, start⟩ =
      .ok (codes, ⟨originalBytes.toByteArray, start + size⟩) ∧
    ((none : Option Nat).isSome || (Core.codesDataIdxs codes).isEmpty) = true := by
  obtain ⟨_, _, _, start, size, _, _, _, _, code⟩ := originalAllFunctionVectors
  refine ⟨start, size, _, code, ?_⟩
  rw [quotedCodeIndicesEmpty]
  rfl

/-- info: 'SqliteWasm.quotedCodeIndicesEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quotedCodeIndicesEmpty
