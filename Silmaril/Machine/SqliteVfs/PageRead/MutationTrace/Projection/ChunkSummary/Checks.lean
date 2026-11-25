module

import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection

private def handle : Handle := ⟨0⟩
private def page : Page := ⟨handle, 2, 3⟩
private def before : FileState := ⟨[1, 2, 3, 10, 11, 12], some .readWrite, 0⟩
private def shrink : Trace := [⟨.truncate handle 5, .ok ()⟩]
private def grow : Trace := [⟨.write handle 6 [90], .ok ()⟩]
private def wipe : Trace := [⟨.truncate handle 0, .ok ()⟩, ⟨.truncate handle 6, .ok ()⟩]

example : (Segment.stream grow).extent.apply 0 = 7 := by decide
example : (Segment.stream grow).extent.apply 8 = 8 := by decide
example : ((Segment.stream shrink).followedBy (Segment.stream grow)).reply before page =
    .ok [10, 11, 0] := by decide
example : ((Segment.stream grow).followedBy (Segment.stream shrink)).reply before page =
    .shortRead [10, 11, 0] := by decide
example : ((Segment.stream (shrink ++ grow)).followedBy (Segment.stream wipe)).reply before page =
    .ok [0, 0, 0] := by decide

example :
    ([[], shrink, grow, wipe, []] : List Trace).foldl
      (fun result trace => result.followedBy (Segment.stream trace)) Segment.empty =
        ⟨.set 6, some 0⟩ := by decide

private def cut : FileState := ⟨[1, 2, 3, 10, 11], some .readWrite, 0⟩
private def regrown : FileState := ⟨[1, 2, 3, 10, 11, 0, 90], some .readWrite, 0⟩

private theorem shrink_grow_valid :
    Trace.Valid (readWrite 16) before ([shrink, [], grow] : List Trace).flatten regrown := by
  change Trace.Valid (readWrite 16) before
    [⟨.truncate handle 5, .ok ()⟩, ⟨.write handle 6 [90], .ok ()⟩] regrown
  exact .cons (middle := cut) rfl (.cons rfl (.nil regrown))

private theorem shrink_grow_covered :
    ∀ exchange ∈ ([shrink, [], grow] : List Trace).flatten, Mutation page exchange := by
  intro exchange membership
  simp [shrink, grow] at membership
  rcases membership with equal | equal
  · cases equal
    exact .truncate 5
  · cases equal
    exact .write 6 [90] (by decide)

example :
    (readWrite 16 regrown page.request).1 =
      (([shrink, [], grow] : List Trace).foldl
        (fun result trace => result.followedBy (Segment.stream trace)) Segment.empty).reply before page :=
  stream_chunks_read [shrink, [], grow] page shrink_grow_valid shrink_grow_covered
    (by decide) (by decide)

#print axioms stream_append
#print axioms stream_chunks
#print axioms stream_chunks_read

end Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary
