module

public import SqliteWasm.WholeModule
public import SqliteWasm.ValidationInputs
import SqliteWasm.ValidationEvidence

public section

namespace SqliteWasm

open Silmaril.Wasm.Validation

/-- All 1,533 defined-function signatures resolve during the ordinary validator's preparation. -/
theorem originalResolvedSignatures :
    (bodyInputs? sqlite).map (fun inputs => inputs.signatures.length) = some 1533 :=
  ValidationEvidence.resolvedSignatures

/-- Defined ordinals 0 through 31 satisfy the Core body rule in the full reactor context. -/
theorem originalFirstBodies :
    ∃ inputs, bodyInputs? sqlite = some inputs ∧
      List.Forall₂ (FuncOk inputs.context) (sqlite.funcs.take 32) (inputs.signatures.take 32) :=
  ValidationEvidence.firstBodies

/-- The isolated version getter at defined ordinal 266 satisfies the same Core body rule. -/
theorem originalVersionBody : BodyValidAt sqlite 266 :=
  ValidationEvidence.versionBody

end SqliteWasm
