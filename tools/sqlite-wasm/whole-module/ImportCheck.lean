module

import SqliteWasm.WholeModule

open SqliteWasm Silmaril.Wasm.Binary

example : Core.decode? originalBytes.toByteArray = some sqlite := originalDecode

/-- info: 'SqliteWasm.originalDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalDecode
