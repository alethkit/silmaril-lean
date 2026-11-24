module

import SqliteWasm.SmallSections

open SqliteWasm SqliteWasmArtifact
open Silmaril.Wasm.Binary.Core.Decode (Sections readModule readSectionBody)

example (state : Sections) : readSectionBody 4 state ⟨originalBytes.toByteArray, 2990⟩ =
    .ok ({ state with tables := sqlite.tables }, ⟨originalBytes.toByteArray, 2997⟩) :=
  originalTableSection.body state

example (state : Sections) : readSectionBody 5 state ⟨originalBytes.toByteArray, 2999⟩ =
    .ok ({ state with memories := sqlite.memories }, ⟨originalBytes.toByteArray, 3002⟩) :=
  originalMemorySection.body state

example (state : Sections) : readSectionBody 6 state ⟨originalBytes.toByteArray, 3004⟩ =
    .ok ({ state with globals := sqlite.globals }, ⟨originalBytes.toByteArray, 3017⟩) :=
  originalGlobalSection.body state

example (state : Sections) : readSectionBody 9 state ⟨originalBytes.toByteArray, 3203⟩ =
    .ok ({ state with elems := sqlite.elems }, ⟨originalBytes.toByteArray, 3880⟩) :=
  originalElementSection.body state

example (state : Sections) (fuel : Nat) :
    readModule.go (fuel + 3) 3 state ⟨originalBytes.toByteArray, 2988⟩ =
      readModule.go fuel 7
        { state with
          tables := sqlite.tables
          memories := sqlite.memories
          globals := sqlite.globals } ⟨originalBytes.toByteArray, 3017⟩ := by
  let withTables : Sections := { state with tables := sqlite.tables }
  let withMemories : Sections := { withTables with memories := sqlite.memories }
  have tableStep : readModule.go (fuel + 3) 3 state ⟨originalBytes.toByteArray, 2988⟩ =
      readModule.go (fuel + 2) 4 withTables ⟨originalBytes.toByteArray, 2997⟩ :=
    originalTableSection.step (fuel + 2) 3 state (by decide)
  have memoryStep : readModule.go (fuel + 2) 4 withTables ⟨originalBytes.toByteArray, 2997⟩ =
      readModule.go (fuel + 1) 5 withMemories ⟨originalBytes.toByteArray, 3002⟩ :=
    originalMemorySection.step (fuel + 1) 4 withTables (by decide)
  have globalStep : readModule.go (fuel + 1) 5 withMemories ⟨originalBytes.toByteArray, 3002⟩ =
      readModule.go fuel 7 { withMemories with globals := sqlite.globals } ⟨originalBytes.toByteArray, 3017⟩ :=
    originalGlobalSection.step fuel 5 withMemories (by decide)
  exact tableStep.trans (memoryStep.trans globalStep)

example (state : Sections) (fuel : Nat) :
    readModule.go (fuel + 1) 8 state ⟨originalBytes.toByteArray, 3200⟩ =
      readModule.go fuel 10 { state with elems := sqlite.elems } ⟨originalBytes.toByteArray, 3880⟩ :=
  originalElementSection.step fuel 8 state (by decide)

/-- info: 'SqliteWasm.originalTableSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalTableSection

/-- info: 'SqliteWasm.originalMemorySection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalMemorySection

/-- info: 'SqliteWasm.originalGlobalSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalGlobalSection

/-- info: 'SqliteWasm.originalElementSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalElementSection
