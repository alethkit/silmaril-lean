module

public import SqliteWasm.Original
public import SqliteWasm.Object
public import Silmaril.Wasm.Binary.Core.Decode
import SqliteWasm.WholeModuleEvidence

public section

namespace SqliteWasm

/-- The ordinary Core decoder on the entire pinned reactor literal returns the quoted module. -/
theorem originalDecode :
    Silmaril.Wasm.Binary.Core.decode? originalBytes.toByteArray = some sqlite :=
  WholeModuleEvidence.originalDecode

end SqliteWasm
