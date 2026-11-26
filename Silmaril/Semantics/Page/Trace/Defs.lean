module

public import Silmaril.Semantics.Page.Defs

/-! Chronological traces of successful accesses to already allocated pages. -/

@[expose] public section
namespace Silmaril.Semantics.Page

universe u v w a
variable {Id : Type u} {Content : Type v} {Memory : Type w}

/-- A read carries its observed value. A write carries the replacement value. -/
inductive AccessEvent (Id : Type u) (Content : Type v) where
  | read (page : Id) (value : Content)
  | write (page : Id) (value : Content)

abbrev Trace (Id : Type u) (Content : Type v) := List (AccessEvent Id Content)
abbrev ReadTrace (Id : Type u) (Content : Type v) := List (Id × Content)
abbrev WriteTrace (Id : Type u) (Content : Type v) := List (Id × Content)

/-- State operations needed by traces. A read leaves the state intact. A write
may fail, and may initialize allocated storage. -/
structure Access (Id : Type u) (Content : Type v) (Memory : Type w) where
  read : Memory → Id → Option Content
  write : Memory → Id → Content → Option Memory

def Store.access (store : Store Id Content Memory) : Access Id Content Memory where
  read memory page := (store.lookup memory page).value
  write memory page value :=
    match store.lookup memory page with
    | .absent => none
    | _ => some (store.set memory page (.defined value))

namespace ReadTrace

def toTrace (reads : ReadTrace Id Content) : Trace Id Content :=
  reads.map fun (page, value) => .read page value

/-- All recorded values agree with one unchanged state. -/
def Agrees (reads : ReadTrace Id Content) (access : Access Id Content Memory)
    (memory : Memory) : Prop :=
  ∀ entry ∈ reads, access.read memory entry.1 = some entry.2

end ReadTrace

namespace WriteTrace

def toTrace (writes : WriteTrace Id Content) : Trace Id Content :=
  writes.map fun (page, value) => .write page value

/-- The successful writes in the page program's edit vocabulary. -/
def edits (writes : WriteTrace Id Content) : List (Edit Id Content) :=
  writes.map fun (page, value) => .write page value

end WriteTrace

namespace Trace

def reads (trace : Trace Id Content) : ReadTrace Id Content :=
  trace.filterMap fun
    | .read page value => some (page, value)
    | .write _ _ => none

def writes (trace : Trace Id Content) : WriteTrace Id Content :=
  trace.filterMap fun
    | .read _ _ => none
    | .write page value => some (page, value)

def ReadOnly (trace : Trace Id Content) : Prop := trace.reads.toTrace = trace

def WriteOnly (trace : Trace Id Content) : Prop := trace.writes.toTrace = trace

def Reads (trace : Trace Id Content) (page : Id) : Prop :=
  ∃ value, (page, value) ∈ trace.reads

/-- Pages assigned at least once. -/
def Defs (trace : Trace Id Content) (page : Id) : Prop :=
  ∃ value, (page, value) ∈ trace.writes

/-- Pages touched by any access, including reads of a value written earlier. -/
def Footprint (trace : Trace Id Content) (page : Id) : Prop := trace.Reads page ∨ trace.Defs page

/-- A page is used from the initial state if it is read before its first write.
A page can be in both the use and def sets. -/
def Uses : Trace Id Content → Id → Prop
  | [], _ => False
  | .read p _ :: rest, page => page = p ∨ Uses rest page
  | .write p _ :: rest, page => page ≠ p ∧ Uses rest page

/-- Replay relates the initial state to the state after the last event.
A read must match the state at its own position in the trace. -/
def Replays (access : Access Id Content Memory) : Trace Id Content → Memory → Memory → Prop
  | [], initial, final => initial = final
  | .read page value :: rest, initial, final =>
      access.read initial page = some value ∧ Replays access rest initial final
  | .write page value :: rest, initial, final =>
      ∃ next, access.write initial page value = some next ∧ Replays access rest next final

/-- Consistency with a specified initial state. -/
def Consistent (trace : Trace Id Content) (access : Access Id Content Memory)
    (initial : Memory) : Prop :=
  ∃ final, trace.Replays access initial final

/-- Both endpoints refine client-selected structure predicates. -/
def Validates (trace : Trace Id Content) (access : Access Id Content Memory)
    (before after : Memory → Prop) : Prop :=
  ∃ initial final, before initial ∧ trace.Replays access initial final ∧ after final

/-- The executable counterpart of replay when page equality is decidable. -/
def run [DecidableEq Content] (access : Access Id Content Memory) :
    Trace Id Content → Memory → Option Memory
  | [], initial => some initial
  | .read page value :: rest, initial =>
      if access.read initial page = some value then run access rest initial else none
  | .write page value :: rest, initial =>
      (access.write initial page value).bind (run access rest)

end Trace

/-- A normally returning path through a page program, with actual read replies
recorded and store validation supplied separately by trace replay.
The path uses reads and writes on a fixed domain. -/
inductive Program.Records {α : Type a} : Program Id Content α → Trace Id Content → α → Prop
  | pure {value} : Records (.pure value) [] value
  | left {l r trace result} : Records l trace result → Records (.choose l r) trace result
  | right {l r trace result} : Records r trace result → Records (.choose l r) trace result
  | read {page value next trace result} : Records (next (.value value)) trace result →
      Records (.call (.read page) next) (.read page value :: trace) result
  | write {page value next trace result} : Records (next .written) trace result →
      Records (.call (.write page value) next) (.write page value :: trace) result

end Silmaril.Semantics.Page
