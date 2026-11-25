module

public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.Defs
import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary

private theorem extent_compose (first second : ExtentEffect) (initial : Nat) :
    (first.followedBy second).apply initial = second.apply (first.apply initial) := by
  cases first <;> cases second <;> simp [ExtentEffect.followedBy, ExtentEffect.apply, Nat.max_assoc]

private def preserves (segment : Segment) (index : Nat) : Prop :=
  ∀ bound ∈ segment.truncateBound, index < bound

private theorem preserves_compose (first second : Segment) (index : Nat) :
    preserves (first.followedBy second) index ↔ preserves first index ∧ preserves second index := by
  cases first with
  | mk left l =>
    cases second with
    | mk right r =>
      cases l <;> cases r <;> simp [preserves, Segment.followedBy, Nat.lt_min]

private theorem extent_single (exchange : Exchange) (initial : Nat) :
    (Segment.single exchange).extent.apply initial = projectedExtent.step initial exchange := by
  rcases exchange with ⟨request, response⟩
  cases request <;> simp [Segment.single, Segment.empty, ExtentEffect.apply, projectedExtent.step]

private theorem preserves_single (exchange : Exchange) (index : Nat) :
    preserves (Segment.single exchange) index ↔ keepsIndex index exchange = true := by
  rcases exchange with ⟨request, response⟩
  cases request <;> simp [Segment.single, Segment.empty, preserves, keepsIndex]

private def Segment.ofTrace : Trace → Segment
  | [] => .empty
  | exchange :: rest => (Segment.single exchange).followedBy (ofTrace rest)

private theorem extent_exact (trace : Trace) (initial : Nat) :
    (Segment.ofTrace trace).extent.apply initial = projectedExtent trace initial := by
  induction trace generalizing initial with
  | nil => simp [Segment.ofTrace, Segment.empty, ExtentEffect.apply, projectedExtent]
  | cons exchange rest ih =>
    change (((Segment.single exchange).extent.followedBy (Segment.ofTrace rest).extent).apply initial) =
      projectedExtent rest (projectedExtent.step initial exchange)
    rw [extent_compose, extent_single, ih]

private theorem preserves_exact (trace : Trace) (index : Nat) :
    preserves (Segment.ofTrace trace) index ↔ trace.all (keepsIndex index) = true := by
  induction trace with
  | nil => simp [Segment.ofTrace, Segment.empty, preserves]
  | cons exchange rest ih =>
    simp only [Segment.ofTrace, preserves_compose, preserves_single, ih, List.all_cons, Bool.and_eq_true]

private theorem keeps_preserves (segment : Segment) (index : Nat) :
    segment.keeps index = true ↔ preserves segment index := by
  cases segment with
  | mk extent bound =>
    cases bound <;> simp [Segment.keeps, preserves]

private theorem summary_reply (trace : Trace) (before : FileState) (page : Page) :
    (Segment.ofTrace trace).reply before page = projectedRead before trace page := by
  have extent := extent_exact trace before.bytes.length
  have byte (index : Nat) :
      (Segment.ofTrace trace).byte? before index = projectedByte? before trace index := by
    have kept := (keeps_preserves (Segment.ofTrace trace) index).trans (preserves_exact trace index)
    simp only [Segment.byte?, extent, projectedByte?, kept]
  simp only [Segment.reply, projectedRead, extent, byte]

theorem extent_followedBy_assoc (a b c : ExtentEffect) :
    (a.followedBy b).followedBy c = a.followedBy (b.followedBy c) := by
  cases a <;> cases b <;> cases c <;> simp [ExtentEffect.followedBy, Nat.max_assoc]

theorem segment_followedBy_assoc (a b c : Segment) :
    (a.followedBy b).followedBy c = a.followedBy (b.followedBy c) := by
  rcases a with ⟨ae, leftBound⟩
  rcases b with ⟨be, bt⟩
  rcases c with ⟨ce, ct⟩
  cases leftBound <;> cases bt <;> cases ct <;>
    simp [Segment.followedBy, extent_followedBy_assoc, Nat.min_assoc]

theorem segment_empty_followedBy (x : Segment) : Segment.empty.followedBy x = x := by
  rcases x with ⟨extent, bound⟩
  cases extent <;> simp [Segment.empty, Segment.followedBy, ExtentEffect.followedBy]

theorem segment_followedBy_empty (x : Segment) : x.followedBy Segment.empty = x := by
  rcases x with ⟨extent, bound⟩
  cases bound <;> cases extent <;> simp [Segment.empty, Segment.followedBy, ExtentEffect.followedBy]

private theorem stream_from (trace : Trace) (start : Segment) :
    trace.foldl (fun result exchange => result.followedBy (.single exchange)) start =
      start.followedBy (Segment.ofTrace trace) := by
  induction trace generalizing start with
  | nil => simp [Segment.ofTrace, segment_followedBy_empty]
  | cons exchange rest ih =>
    rw [List.foldl_cons, ih, Segment.ofTrace, segment_followedBy_assoc]

private theorem stream_eq (trace : Trace) : Segment.stream trace = Segment.ofTrace trace := by
  rw [Segment.stream, stream_from, segment_empty_followedBy]

theorem stream_append (left right : Trace) :
    Segment.stream (left ++ right) = (Segment.stream left).followedBy (Segment.stream right) := by
  rw [Segment.stream, List.foldl_append, stream_from, stream_eq right]
  rfl

private theorem stream_chunks_from (chunks : List Trace) (start : Segment) :
    chunks.foldl (fun result trace => result.followedBy (Segment.stream trace)) start =
      start.followedBy (Segment.stream chunks.flatten) := by
  induction chunks generalizing start with
  | nil => simp [Segment.stream, segment_followedBy_empty]
  | cons chunk chunks ih =>
    rw [List.foldl_cons, ih, List.flatten_cons, stream_append, segment_followedBy_assoc]

/-- Summarize arbitrary ordered chunks independently, then combine only the
summaries. This recovers the exact summary of the flattened trace. -/
theorem stream_chunks (chunks : List Trace) :
    chunks.foldl (fun result trace => result.followedBy (Segment.stream trace)) Segment.empty =
      Segment.stream chunks.flatten := by
  rw [stream_chunks_from, segment_empty_followedBy]

theorem stream_chunks_read {capacity : Nat} {before after : FileState}
    (chunks : List Trace) (page : Page)
    (valid : Trace.Valid (readWrite capacity) before chunks.flatten after)
    (allowed : ∀ exchange ∈ chunks.flatten, Mutation page exchange)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false) :
    (readWrite capacity after page.request).1 =
      (chunks.foldl (fun result trace => result.followedBy (Segment.stream trace)) Segment.empty).reply
        before page := by
  rw [stream_chunks, stream_eq]
  exact (trace_read_reply page valid allowed admitted live).trans (summary_reply chunks.flatten before page).symm

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary
