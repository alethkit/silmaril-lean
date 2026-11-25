module

public import SqliteWasm.ReactorValidation
import SqliteWasm.GuardEvidence

public section

namespace SqliteWasm

open Silmaril.Wasm.Validation

/-- For the pinned reactor, ordinary validation succeeds once all ordered body checks pass. -/
theorem originalValidateOfBodies
    (bodies : (bodyInputs? sqlite).any (fun inputs =>
      allPairs (defaultCheckers.func inputs.context) sqlite.funcs inputs.signatures) = true) :
    (validate? sqlite).isSome = true :=
  GuardEvidence.finalize bodies

end SqliteWasm
