module

import SqliteWasm.MetadataVectors

open SqliteWasm SqliteWasmArtifact
open Silmaril.Wasm.Binary.Core.Decode (Sections readModule readSectionBody)

example (state : Sections) : readSectionBody 1 state ⟨originalBytes.toByteArray, 11⟩ =
    .ok ({ state with types := sqlite.types }, ⟨originalBytes.toByteArray, 529⟩) :=
  originalTypeSection.body state

example (state : Sections) : readSectionBody 2 state ⟨originalBytes.toByteArray, 532⟩ =
    .ok ({ state with imports := sqlite.imports }, ⟨originalBytes.toByteArray, 1450⟩) :=
  originalImportSection.body state

example (state : Sections) : readSectionBody 7 state ⟨originalBytes.toByteArray, 3020⟩ =
    .ok ({ state with exports := sqlite.exports }, ⟨originalBytes.toByteArray, 3200⟩) :=
  originalExportSection.body state

example (state : Sections) (fuel : Nat) :
    readModule.go (fuel + 2) 0 state ⟨originalBytes.toByteArray, 8⟩ =
      readModule.go fuel 2 { state with types := sqlite.types, imports := sqlite.imports }
        ⟨originalBytes.toByteArray, 1450⟩ :=
  (originalTypeSection.step (fuel + 1) 0 state (by decide)).trans
    (originalImportSection.step fuel 1 { state with types := sqlite.types } (by decide))

example (state : Sections) (fuel : Nat) :
    readModule.go (fuel + 1) 7 state ⟨originalBytes.toByteArray, 3017⟩ =
      readModule.go fuel 8 { state with exports := sqlite.exports } ⟨originalBytes.toByteArray, 3200⟩ :=
  originalExportSection.step fuel 7 state (by decide)

/-- info: 'SqliteWasm.originalTypeSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalTypeSection

/-- info: 'SqliteWasm.originalImportSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalImportSection

/-- info: 'SqliteWasm.originalExportSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalExportSection
