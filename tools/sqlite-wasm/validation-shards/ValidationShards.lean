module

public import SqliteWasm.ReactorValidation
import SqliteWasm.ShardEvidence

public section

namespace SqliteWasm

open Silmaril.Wasm.Validation

/-- The ordinary body checker accepts defined ordinals 32–71 in the full reactor context. -/
theorem originalAdditionalBodyChecks {inputs : BodyInputs} (prepared : bodyInputs? sqlite = some inputs) :
    allPairs (defaultCheckers.func inputs.context)
      ((sqlite.funcs.drop 32).take 40) ((inputs.signatures.drop 32).take 40) = true :=
  ShardEvidence.additionalBodies prepared

/-- Defined ordinals 0–71 satisfy the Core body rule with their corresponding resolved signatures. -/
theorem originalFirst72Bodies :
    ∃ inputs, bodyInputs? sqlite = some inputs ∧
      List.Forall₂ (FuncOk inputs.context) (sqlite.funcs.take 72) (inputs.signatures.take 72) :=
  ShardEvidence.first72Bodies

end SqliteWasm
