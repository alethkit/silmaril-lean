module

public import Silmaril.Containers.SqliteVfs.ReadEntry.Defs
public import Init.Data.List.OfFn

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.ReadReturn

open Silmaril.Machine
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary (FileBinding)
open Silmaril.Machine.SqliteRead (BufferView Status)

/-- Read the whole destination span in increasing address order. -/
def bufferBytes? (request : SqliteRead.Request) (after : BufferView) : Option Bytes :=
  List.ofFnM fun i : Fin request.amount.toNat =>
    (after (request.buffer.toNat + i.val)).map UInt8.ofBitVec

/-- Recover a typed exchange from a supplied return status and destination
buffer. An unsupported status, unbound pointer, or missing byte gives none. -/
def projectReturn (binding : FileBinding) (request : SqliteRead.Request)
    (after : BufferView) (status : Status) : Option Exchange := do
  let handle ← binding request.file
  let reply ← match status with
    | .ok => (bufferBytes? request after).map ReadReply.ok
    | .shortRead => (bufferBytes? request after).map ReadReply.shortRead
    | .other _ => none
  pure ⟨.read handle request.offset.toNat request.amount.toNat, reply⟩

end Silmaril.Containers.SqliteVfs.ReadReturn
