module

public import SqliteWasm.CodeCoverage
public import SqliteWasm.Object
public import SqliteWasm.Original
import SqliteWasm.VectorBridge

public section

namespace SqliteWasm

/-- The original Function and Code vectors decode to the quoted records at every defined ordinal. -/
theorem originalAllFunctionVectors : SqliteWasmArtifact.DecodesAllFunctionVectors original sqlite.funcs :=
  VectorBridge.originalAllFunctionVectors

end SqliteWasm
