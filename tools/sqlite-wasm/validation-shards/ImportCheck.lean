module

import SqliteWasm.ValidationShards

open SqliteWasm Silmaril.Wasm.Binary Silmaril.Wasm.Validation

example : ∃ m inputs, Core.decode? originalBytes.toByteArray = some m ∧
    bodyInputs? m = some inputs ∧
    List.Forall₂ (FuncOk inputs.context) (m.funcs.take 72) (inputs.signatures.take 72) ∧
    allPairs (defaultCheckers.func inputs.context)
      ((m.funcs.drop 32).take 40) ((inputs.signatures.drop 32).take 40) = true ∧
    BodyValidAt m 266 := by
  obtain ⟨inputs, prepared, checked⟩ := originalFirst72Bodies
  exact ⟨sqlite, inputs, originalDecode, prepared, checked, originalAdditionalBodyChecks prepared,
    originalVersionBody⟩

example : sqlite.funcs.take 72 = Code0000.funcs := rfl

example : Code0000.funcs.length = 72 := rfl

/-- info: 'SqliteWasm.originalAdditionalBodyChecks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalAdditionalBodyChecks

/-- info: 'SqliteWasm.originalFirst72Bodies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalFirst72Bodies
