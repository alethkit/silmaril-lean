module

public import Silmaril.Containers.SqliteVfs.ReadReturn.Defs
import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms
import Init.Data.UInt.Lemmas

public section

namespace Silmaril.Proofs.Containers.SqliteVfs.ReadReturn

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.ReadEntry (projectEntry)
open Silmaril.Machine
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
open Silmaril.Machine.SqliteRead (BufferView Status)
open Silmaril.Containers.SqliteVfs.ReadReturn

private theorem bufferBytes_eq {request : SqliteRead.Request} {after : BufferView}
    (bytes : Bytes) (offset count : Nat) (amount : request.amount.toNat = count)
    (writes : ∀ i, i < count →
      after (request.buffer.toNat + i) = ((readBytes bytes offset count)[i]?).map UInt8.toBitVec) :
    bufferBytes? request after = some (readBytes bytes offset count) := by
  subst count
  have atIndex (i : Fin request.amount.toNat) :
      (after (request.buffer.toNat + i.val)).map UInt8.ofBitVec =
        some (bytes[offset + i.val]?.getD 0) := by
    rw [writes _ i.isLt]
    simp [readBytes, i.isLt]
  unfold bufferBytes?
  simp_rw [atIndex]
  exact List.ofFnM_pure (m := Option)

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
      (runtime (readOnly capacity)).beh file (.blocked (encode [exchange])) := by
  let outcome := fill (readOnly capacity) file cache target page
  let bytes := readBytes file.bytes page.offset page.size
  have requestEq :
      Request.read page.handle request.offset.toNat request.amount.toNat = page.request := by
    simp [Page.request, aligned.offset, aligned.amount]
  have finish (reply : Response page.request)
      (projected : projectReturn binding request after status = some ⟨page.request, reply⟩)
      (trace : outcome.trace = [⟨page.request, reply⟩]) :
      ∃ exchange, projectReturn binding request after status = some exchange ∧
        projectEntry binding (SqliteRead.dispatch request) = some (.recv exchange.request) ∧
        outcome.trace = [exchange] ∧
        (machine (readOnly capacity)).Exec Mach.seqPolicy (.idle file) (encode [exchange])
          (.idle outcome.file) ∧
        (runtime (readOnly capacity)).beh file (.blocked (encode [exchange])) := by
    have valid : Trace.Valid (readOnly capacity) file outcome.trace outcome.file :=
      fill_trace (readOnly capacity) file cache target page
    rw [trace] at valid
    refine ⟨⟨page.request, reply⟩, projected, ?_, trace, ?_, ?_⟩
    · simp [projectEntry, SqliteRead.dispatch, aligned.handle, requestEq]
    · exact exec_iff.mpr ⟨_, _, valid, .inl ⟨rfl, rfl⟩⟩
    · exact blocked_iff.mpr ⟨_, _, valid, rfl⟩
  have bridge := returning_handler_agrees_with_fill request page env file capacity cache target
    before after status admitted aligned positive live owned law
  rcases supported with rfl | rfl
  · have copied := bufferBytes_eq file.bytes page.offset page.size aligned.amount bridge.2.2
    refine finish (.ok bytes) ?_ (congrArg Outcome.trace bridge.2.1)
    simp [projectReturn, aligned.handle, copied, bytes]
    congr
  · have copied := bufferBytes_eq file.bytes page.offset page.size aligned.amount bridge.2.2
    refine finish (.shortRead bytes) ?_ (congrArg Outcome.trace bridge.2.1)
    simp [projectReturn, aligned.handle, copied, bytes]
    congr

end Silmaril.Proofs.Containers.SqliteVfs.ReadReturn
