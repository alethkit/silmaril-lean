module

import SqliteWasm.ValidationGuards

open SqliteWasm Silmaril.Wasm.Binary Silmaril.Wasm.Validation

example (bodies : (bodyInputs? sqlite).any (fun inputs =>
    allPairs (defaultCheckers.func inputs.context) sqlite.funcs inputs.signatures) = true) :
    ∃ m, Core.decode? originalBytes.toByteArray = some m ∧ ModuleValid m :=
  ⟨sqlite, originalDecode, validate_sound (originalValidateOfBodies bodies)⟩

/-- info: 'SqliteWasm.originalValidateOfBodies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalValidateOfBodies
