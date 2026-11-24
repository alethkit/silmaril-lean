module

import SqliteWasm.AllFunctionVectors

open SqliteWasm SqliteWasmArtifact

example : DecodesAllFunctionVectors original sqlite.funcs := originalAllFunctionVectors

/-- info: 'SqliteWasm.originalAllFunctionVectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalAllFunctionVectors
