module

import SqliteWasm.DataSection

open SqliteWasm SqliteWasmArtifact
open Silmaril.Wasm.Binary.Core.Decode (Sections readModule readSectionBody)

example (state : Sections) : readSectionBody 11 state ⟨originalBytes.toByteArray, 683406⟩ =
    .ok ({ state with data := sqlite.data }, ⟨originalBytes.toByteArray, 741717⟩) :=
  originalDataSection.body state

example (state : Sections) (fuel : Nat) :
    readModule.go (fuel + 1) 12 state ⟨originalBytes.toByteArray, 683402⟩ =
      readModule.go fuel 13 { state with data := sqlite.data } ⟨originalBytes.toByteArray, 741717⟩ :=
  originalDataSection.step fuel 12 state (by decide)

/-- info: 'SqliteWasm.originalDataSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalDataSection
