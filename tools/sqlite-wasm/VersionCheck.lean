module

public import SqliteWasm.VersionModel

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

theorem version_body :
    versionFunction?.map Func.body = some [.intConst .i32 versionNumber] := rfl

theorem version_exec {H : Type} (store : Store H) (frame : Frame) :
    runVersion store frame = some (store, frame, .normal [Binaryen.ofInt .i32 versionNumber]) :=
  rfl

#print axioms version_body
#print axioms version_exec

end SqliteWasm
