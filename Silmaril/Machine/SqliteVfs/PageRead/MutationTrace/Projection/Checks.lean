module

import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def handle : Handle := ⟨0⟩
private def page : Page := ⟨handle, 2, 3⟩
private def original : FileState := ⟨[1, 2, 3, 10, 11, 12], some .readWrite, 0⟩
private def shrunk : FileState := ⟨[1, 2, 3, 10, 11], some .readWrite, 0⟩
private def regrown : FileState := ⟨[1, 2, 3, 10, 11, 0, 90], some .readWrite, 0⟩
private def shrink : Trace := [⟨.truncate handle 5, .ok ()⟩]
private def regrow : Trace := shrink ++ [⟨.write handle 6 [90], .ok ()⟩]

private theorem shrinkValid : Trace.Valid (readWrite 16) original shrink shrunk :=
  .cons rfl (.nil shrunk)

private theorem shrinkCovered (exchange : Exchange) (member : exchange ∈ shrink) : Mutation page exchange := by
  have equal : exchange = ⟨.truncate handle 5, .ok ()⟩ := by simpa [shrink] using member
  subst exchange
  exact .truncate 5

private theorem regrowValid : Trace.Valid (readWrite 16) original regrow regrown :=
  .cons (middle := shrunk) rfl (.cons rfl (.nil regrown))

private theorem regrowCovered (exchange : Exchange) (member : exchange ∈ regrow) : Mutation page exchange := by
  simp [regrow] at member
  rcases member with truncation | rfl
  · exact shrinkCovered exchange truncation
  · exact .write 6 [90] (.inl (by decide))

example : (readWrite 16 shrunk page.request).1 = .shortRead [10, 11, 0] :=
  trace_read_reply page shrinkValid shrinkCovered (by decide) rfl

example : shrunk.bytes[5]? = none :=
  trace_optional_byte page 2 (by decide) shrinkValid shrinkCovered

example : (readWrite 16 regrown page.request).1 = .ok [10, 11, 0] :=
  trace_read_reply page regrowValid regrowCovered (by decide) rfl

example : regrown.bytes[3]? = some 10 :=
  trace_optional_byte page 0 (by decide) regrowValid regrowCovered

example : regrown.bytes[5]? = some 0 :=
  trace_optional_byte page 2 (by decide) regrowValid regrowCovered

private def erased : FileState := ⟨[], some .readWrite, 0⟩
private def extended : FileState := ⟨[0, 0, 0, 0, 0, 0], some .readWrite, 0⟩
private def eraseRegrow : Trace := [⟨.truncate handle 0, .ok ()⟩, ⟨.truncate handle 6, .ok ()⟩]

example : (readWrite 16 extended page.request).1 = .ok [0, 0, 0] := by
  have valid : Trace.Valid (readWrite 16) original eraseRegrow extended :=
    .cons (middle := erased) rfl (.cons rfl (.nil extended))
  have covered (exchange : Exchange) (member : exchange ∈ eraseRegrow) : Mutation page exchange := by
    simp [eraseRegrow] at member
    rcases member with rfl | rfl
    · exact .truncate 0
    · exact .truncate 6
  exact trace_read_reply page valid covered (by decide) rfl

#print axioms trace_extent_mode
#print axioms trace_optional_byte
#print axioms trace_read_reply

end Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection
