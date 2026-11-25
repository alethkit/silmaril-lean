module

public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ByTrace

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- The extent fold reconstructs the final file length and the successful
mutations preserve the selected handle mode. -/
theorem trace_extent_mode {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, Mutation page exchange) :
    after.bytes.length = projectedExtent trace before.bytes.length ∧
      after.mode page.handle = before.mode page.handle :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.trace_extent_mode
    page valid allowed

/-- The projected byte exactly matches the final value and presence at a
requested index. -/
theorem trace_optional_byte {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page) (index : Nat) (inside : index < page.size)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, Mutation page exchange) :
    after.bytes[page.offset + index]? = projectedByte? before trace (page.offset + index) :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.trace_optional_byte
    page index inside valid allowed

/-- The extent and byte projections determine the complete typed reply to
a final admitted live read on the bounded backing. -/
theorem trace_read_reply {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, Mutation page exchange)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false) :
    (readWrite capacity after page.request).1 = projectedRead before trace page :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection.trace_read_reply
    page valid allowed admitted live

end Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection
