module

public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.ByChunk

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection

/-- Combining three summaries preserves their order and is associative. -/
theorem segment_followedBy_assoc (a b c : Segment) :
    (a.followedBy b).followedBy c = a.followedBy (b.followedBy c) :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.segment_followedBy_assoc a b c

/-- An empty preceding chunk leaves the summary unchanged. -/
theorem segment_empty_followedBy (x : Segment) : Segment.empty.followedBy x = x :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.segment_empty_followedBy x

/-- An empty following chunk leaves the summary unchanged. -/
theorem segment_followedBy_empty (x : Segment) : x.followedBy Segment.empty = x :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.segment_followedBy_empty x

/-- Concatenating traces combines their independently computed summaries. -/
theorem stream_append (left right : Trace) :
    Segment.stream (left ++ right) = (Segment.stream left).followedBy (Segment.stream right) :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.stream_append left right

/-- Summarize each chunk and combine in order to recover the exact summary of the flattened trace. -/
theorem stream_chunks (chunks : List Trace) :
    chunks.foldl (fun result trace => result.followedBy (Segment.stream trace)) Segment.empty =
      Segment.stream chunks.flatten :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.stream_chunks chunks

/-- For a valid covered bounded history, ordered chunk summaries recover the exact final typed read. -/
theorem stream_chunks_read {capacity : Nat} {before after : FileState}
    (chunks : List Trace) (page : Page)
    (valid : Trace.Valid (readWrite capacity) before chunks.flatten after)
    (allowed : ∀ exchange ∈ chunks.flatten, Mutation page exchange)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false) :
    (readWrite capacity after page.request).1 =
      (chunks.foldl (fun result trace => result.followedBy (Segment.stream trace)) Segment.empty).reply
        before page :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.stream_chunks_read chunks page valid allowed admitted live

end Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary
