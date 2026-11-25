module

public import Silmaril.Containers.SqliteVfs.ReadReturn.Defs
import Silmaril.Proofs.Containers.SqliteVfs.ReadReturn.Completion

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.ReadReturn

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.ReadEntry (projectEntry)
open Silmaril.Machine
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
open Silmaril.Machine.SqliteRead (BufferView Status)

/-- A supported return under the stable-snapshot handler law gives the exact
PageRead exchange and completes the logical container request. -/
theorem returning_handler_completes {binding : FileBinding}
    (request : SqliteRead.Request) (page : Page) (env : SqliteRead.Context) (file : FileState)
    (capacity : Nat) (cache : Cache) (target : SlotId) (before after : BufferView) (status : Status)
    (admitted : env.Admits request) (aligned : MatchesPage binding request page) (positive : 0 < page.number)
    (live : (file.mode page.handle).isNone = false) (owned : cache target = some .vacant)
    (law : SqliteRead.Handler (file.bytes.map UInt8.toBitVec) request before after status)
    (supported : status = .ok ∨ status = .shortRead) :
    let outcome := fill (readOnly capacity) file cache target page
    ∃ exchange, projectReturn binding request after status = some exchange ∧
      projectEntry binding (SqliteRead.dispatch request) = some (.recv exchange.request) ∧
      outcome.trace = [exchange] ∧
      (machine (readOnly capacity)).Exec Mach.seqPolicy (.idle file) (encode [exchange])
        (.idle outcome.file) ∧
      (runtime (readOnly capacity)).beh file (.blocked (encode [exchange])) :=
  Proofs.Containers.SqliteVfs.ReadReturn.returning_handler_completes request page env file capacity
    cache target before after status admitted aligned positive live owned law supported

end Silmaril.Containers.SqliteVfs.ReadReturn
