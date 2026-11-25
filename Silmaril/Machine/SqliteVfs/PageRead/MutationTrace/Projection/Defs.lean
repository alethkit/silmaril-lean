module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Completed mutations in the bounded backing on the selected handle. Any
write interval must be disjoint from the requested page. -/
inductive Mutation (page : Page) : Exchange → Prop where
  | write (offset : Int) (data : Bytes)
      (apart : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset) :
      Mutation page ⟨.write page.handle offset data, .ok ()⟩
  | truncate (size : Int) : Mutation page ⟨.truncate page.handle size, .ok ()⟩

/-- A truncate keeps an index strictly below its requested extent.
Other covered mutations keep every original index outside their writes. -/
def keepsIndex (index : Nat) (exchange : Exchange) : Bool :=
  match exchange.request with
  | .truncate _ size => decide (index < size.toNat)
  | _ => true

/-- File length after the covered operations. Each successful write grows
only as needed and each successful truncate sets the length. -/
def projectedExtent (trace : Trace) (initial : Nat) : Nat := trace.foldl step initial
where
  step (length : Nat) (exchange : Exchange) : Nat :=
    match exchange.request with
    | .write _ offset data => max length (offset.toNat + data.length)
    | .truncate _ size => size.toNat
    | _ => length

/-- Project a covered optional byte from the starting snapshot and trace. -/
def projectedByte? (file : FileState) (trace : Trace) (index : Nat) : Option UInt8 :=
  if index < projectedExtent trace file.bytes.length then
    some (if trace.all (keepsIndex index) then file.bytes[index]?.getD 0 else 0)
  else none

/-- Project the typed padded reply of an admitted final page read. -/
def projectedRead (file : FileState) (trace : Trace) (page : Page) : ReadReply :=
  let buffer := List.ofFn fun i : Fin page.size => (projectedByte? file trace (page.offset + i)) |>.getD 0
  if page.offset + page.size ≤ projectedExtent trace file.bytes.length then .ok buffer else .shortRead buffer

end Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection
