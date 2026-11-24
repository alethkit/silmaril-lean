module

public import SqliteWasm.Object
public import SqliteWasm.BodyComposition
import SqliteWasm.DataIndicesEvidence

public section

namespace SqliteWasm

open SqliteWasmArtifact Silmaril.Wasm.Binary

/-- The quoted Code vector passes the Core decoder's guard when Data Count is absent. -/
theorem quotedCodeIndicesEmpty : Core.codesDataIdxs (sqlite.funcs.map functionCode) = [] :=
  DataIndicesEvidence.quotedCodeIndicesEmpty

end SqliteWasm
