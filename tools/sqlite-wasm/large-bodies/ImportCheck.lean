module

import SqliteWasm.LargeBodies

open SqliteWasm SqliteWasmArtifact

example : ReadsCodeAt original 99 (sqlite.funcs.map functionCode)[99]! := originalCode99
example : ReadsCodeAt original 260 (sqlite.funcs.map functionCode)[260]! := originalCode260
example : ReadsCodeAt original 719 (sqlite.funcs.map functionCode)[719]! := originalCode719
example : ReadsCodeAt original 767 (sqlite.funcs.map functionCode)[767]! := originalCode767

/-- info: 'SqliteWasm.originalCode99' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalCode99

/-- info: 'SqliteWasm.originalCode260' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalCode260

/-- info: 'SqliteWasm.originalCode719' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalCode719

/-- info: 'SqliteWasm.originalCode767' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalCode767
