module
public import Silmaril.Formats.Sqlite.VirtualTable.Defs

/-! An immutable one-column table for
`WHERE rowid >= lower AND value < ceiling ORDER BY rowid`.
The module enforces the lower bound and emits rows in the requested direction.
The ceiling is passed as the first argument but left for the caller to recheck. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.VirtualTable.Backed

def input (dir : Direction) : BestIndexInput 1 :=
  ⟨[⟨.rowid, .ge, true⟩, ⟨.value 0, .lt, true⟩], some dir⟩

def query (dir : Direction) (lower ceiling : Int64) : Query 1 :=
  ⟨input dir, #v[lower, ceiling]⟩

def key (dir : Direction) : IndexKey :=
  ⟨if dir == .asc then 1 else 2, some "bounded"⟩

def plan (dir : Direction) : Plan :=
  ⟨key dir, [⟨1, false⟩, ⟨0, true⟩], true⟩

def candidates (snapshot : Snapshot 1) (dir : Direction) (lower : Int64) : Relation 1 :=
  dir.sort (snapshot.rows.filter fun row => Operator.ge.test row.rowid lower)

def index (dir : Direction) : Index 1 := fun snapshot argv =>
  match argv with
  | [_, lower] => .ok (candidates snapshot dir lower)
  | _ => .error .argumentCount

def implementation : Module 1 where
  bestIndex info := do
    let some dir := info.orderBy | throw .noPlan
    if info == input dir then return plan dir else throw .noPlan
  index candidate :=
    if candidate == key .asc then some (index .asc)
    else if candidate == key .desc then some (index .desc)
    else none

def table (snapshot : Snapshot 1) : Table 1 := ⟨implementation, snapshot⟩

end Silmaril.Formats.Sqlite.VirtualTable.Backed
