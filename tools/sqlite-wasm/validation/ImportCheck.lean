module

import SqliteWasm.ReactorValidation

open SqliteWasm Silmaril.Wasm.Binary Silmaril.Wasm.Validation

example : ∃ m, Core.decode? originalBytes.toByteArray = some m ∧
    (bodyInputs? m).map (fun inputs => inputs.signatures.length) = some 1533 ∧
    (∃ inputs, bodyInputs? m = some inputs ∧
      List.Forall₂ (FuncOk inputs.context) (m.funcs.take 32) (inputs.signatures.take 32)) ∧
    BodyValidAt m 266 :=
  ⟨sqlite, originalDecode, originalResolvedSignatures, originalFirstBodies, originalVersionBody⟩

example : validate? sqlite = (bodyInputs? sqlite).bind (finishValidation sqlite) :=
  validate_eq_bodyInputs sqlite

/-- info: 'SqliteWasm.originalResolvedSignatures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalResolvedSignatures
/-- info: 'SqliteWasm.originalFirstBodies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalFirstBodies
/-- info: 'SqliteWasm.originalVersionBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms originalVersionBody
/-- info: 'SqliteWasm.validate_eq_bodyInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validate_eq_bodyInputs
