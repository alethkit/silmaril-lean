module

/-! The row-list lookup and read interface shared by the VM, logical models
and physical B-trees. The established namespaces keep existing clients source-compatible. -/
@[expose] public section

namespace Silmaril.Formats.Sqlite.BTree.Abstract

variable {Key Value : Type}

/-- Reference table lookup: the first entry whose key is propositionally equal
to the query. The routing comparator is deliberately separate from equality. -/
def lookupList [DecidableEq Key] (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | (other, value) :: rest => if other = key then some value else lookupList key rest

end Silmaril.Formats.Sqlite.BTree.Abstract

namespace Silmaril.Formats.Sqlite.BTree.Query

variable {Key Row : Type}

/-- A finite keyed table and an implementation of point access. This interface
can be instantiated with an abstract tree, a page cache, or a symbolic model.
Its refinement law concerns the same table, independently of how `get` works. -/
structure ReadModel (Key Row : Type) [DecidableEq Key] where
  entries : List (Key × Row)
  get : Key → Option Row
  get_eq : ∀ key, get key = Abstract.lookupList key entries

namespace ReadModel
variable [DecidableEq Key]

def ofList (entries : List (Key × Row)) : ReadModel Key Row :=
  ⟨entries, fun key => Abstract.lookupList key entries, fun _ => rfl⟩

def rows (model : ReadModel Key Row) : List Row := model.entries.map Prod.snd

/-- Row identifiers are unique; secondary keys need not be. -/
def Unique (model : ReadModel Key Row) : Prop := (model.entries.map Prod.fst).Nodup

instance (model : ReadModel Key Row) : Decidable model.Unique :=
  inferInstanceAs (Decidable (model.entries.map Prod.fst).Nodup)

/-- A table representation preserves the row list, hence duplicates and scan
order. SQL queries without ORDER BY need not promise this particular order. -/
def Represents (model : ReadModel Key Row) (rows : List Row) : Prop := model.rows = rows

end ReadModel

end Silmaril.Formats.Sqlite.BTree.Query
