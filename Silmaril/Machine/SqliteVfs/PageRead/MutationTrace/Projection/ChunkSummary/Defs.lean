module

public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Extent transform of a mutation segment before its starting size is known. -/
inductive ExtentEffect where
  | grow (floor : Nat)
  | set (length : Nat)
  deriving DecidableEq, Repr

def ExtentEffect.apply (initial : Nat) : ExtentEffect → Nat
  | .grow floor => max initial floor
  | .set length => length

def ExtentEffect.followedBy (first second : ExtentEffect) : ExtentEffect :=
  match first, second with
  | _, .set length => .set length
  | .set length, .grow floor => .set (max length floor)
  | .grow low, .grow high => .grow (max low high)

/-- The optional bound is the smallest truncate target in the segment.
Without a truncate, the summary imposes no retention bound. -/
structure Segment where
  extent : ExtentEffect
  truncateBound : Option Nat
  deriving DecidableEq, Repr

def Segment.empty : Segment := ⟨.grow 0, none⟩

/-- Summarize the request shape. The backing theorem supplies the operation's
validity and coverage premises. -/
def Segment.single (exchange : Exchange) : Segment :=
  match exchange.request with
  | .write _ offset data => ⟨.grow (offset.toNat + data.length), none⟩
  | .truncate _ size => ⟨.set size.toNat, some size.toNat⟩
  | _ => .empty

def Segment.followedBy (first second : Segment) : Segment :=
  ⟨first.extent.followedBy second.extent, match first.truncateBound, second.truncateBound with
    | none, bound | bound, none => bound
    | some left, some right => some (min left right)⟩

def Segment.keeps (segment : Segment) (index : Nat) : Bool :=
  match segment.truncateBound with
  | none => true
  | some bound => decide (index < bound)

def Segment.byte? (segment : Segment) (before : FileState) (index : Nat) : Option UInt8 :=
  if index < segment.extent.apply before.bytes.length then
    some (if segment.keeps index then before.bytes[index]?.getD 0 else 0)
  else none

def Segment.reply (segment : Segment) (before : FileState) (page : Page) : ReadReply :=
  let buffer := List.ofFn fun i : Fin page.size => (segment.byte? before (page.offset + i)).getD 0
  if page.offset + page.size ≤ segment.extent.apply before.bytes.length then .ok buffer
  else .shortRead buffer

/-- Summarize a trace in order, without an initial file size. -/
def Segment.stream (trace : Trace) : Segment :=
  trace.foldl (fun result exchange => result.followedBy (.single exchange)) .empty

end Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.ChunkSummary
