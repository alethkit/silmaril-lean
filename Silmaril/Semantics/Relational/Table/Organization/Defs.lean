module

public import Silmaril.Semantics.Relational.Table.Schema.Defs

/-! Rows use dependent functions for cells, with column kinds interpreted by a client.
Both a row index type and a finite row count are available as alignment data. -/

@[expose] public section

namespace Silmaril.Relational

universe u v w x

/-- An ordered collection of rows with a client-selected row representation.
For example, dynamic rows can themselves be lists of values of varying lengths. -/
abbrev UnschematizedTable (DynamicRow : Type u) := List DynamicRow

abbrev Row {I : Type u} {Kind : Type v} (kind : I → Kind) (Cell : Kind → Type w) :=
  (i : I) → Cell (kind i)

abbrev Rows {I : Type u} {Kind : Type v} (RowId : Type x)
    (kind : I → Kind) (Cell : Kind → Type w) :=
  RowId → Row kind Cell

abbrev Columns {I : Type u} {Kind : Type v} (RowId : Type x)
    (kind : I → Kind) (Cell : Kind → Type w) :=
  (i : I) → RowId → Cell (kind i)

/-- Read the same cells in either orientation using their shared row identities. -/
def rowsEquivColumns {I : Type u} {Kind : Type v} {RowId : Type x}
    {kind : I → Kind} {Cell : Kind → Type w} :
    Rows RowId kind Cell ≃ Columns RowId kind Cell where
  toFun rows i r := rows r i
  invFun columns r i := columns i r
  left_inv _ := rfl
  right_inv _ := rfl

/-- A finite order explicitly enumerates row identities. Equal row values can have distinct IDs. -/
def orderRows {RowId : Type x} {I : Type u} {Kind : Type v} {n : Nat}
    {kind : I → Kind} {Cell : Kind → Type w} (order : Fin n ≃ RowId) :
    Rows RowId kind Cell ≃ Rows (Fin n) kind Cell where
  toFun rows i := rows (order i)
  invFun rows r := rows (order.symm r)
  left_inv rows := funext fun r => congrArg rows (order.apply_symm_apply r)
  right_inv rows := funext fun i => congrArg rows (order.symm_apply_apply i)

abbrev Table {I : Type u} {Kind : Type v} (kind : I → Kind) (Cell : Kind → Type w) :=
  List (Row kind Cell)

/-- List columns carry a common length witness, even when there are no columns. -/
structure AlignedColumns {I : Type u} {Kind : Type v} (kind : I → Kind) (Cell : Kind → Type w) where
  rowCount : Nat
  values : (i : I) → List (Cell (kind i))
  length_eq : ∀ i, (values i).length = rowCount

namespace AlignedColumns

variable {I : Type u} {Kind : Type v} {kind : I → Kind} {Cell : Kind → Type w}

def ofRows (rows : Table kind Cell) : AlignedColumns kind Cell where
  rowCount := rows.length
  values i := rows.map (fun row => row i)
  length_eq i := List.length_map (as := rows) (fun row => row i)

def toRows (columns : AlignedColumns kind Cell) : Table kind Cell :=
  List.ofFn fun r : Fin columns.rowCount =>
    fun i => (columns.values i).get (r.cast (columns.length_eq i).symm)

@[ext] theorem ext {a b : AlignedColumns kind Cell}
    (hCount : a.rowCount = b.rowCount) (hValues : a.values = b.values) : a = b := by
  cases a; cases b; cases hCount; cases hValues; rfl

end AlignedColumns

/-- A column map with a kind projection induces a contravariant row operation. -/
def ColumnMap.pullRow {I : Type u} {J : Type v} {Label : Type w} {Kind : Type x}
    {source : I → Label} {target : J → Label} (map : ColumnMap source target)
    (kind : Label → Kind) {Cell : Kind → Type*} (row : Row (kind ∘ target) Cell) :
    Row (kind ∘ source) Cell :=
  fun i => cast (congrArg (Cell ∘ kind) (map.label_eq i)) (row (map.index i))

/-- Erase positional type information, preserving row and cell sequence. -/
def PositionalSchema.eraseTable {Kind : Type v} {Cell : Kind → Type w} {Value : Type x}
    (schema : PositionalSchema Kind) (encode : (k : Kind) → Cell k → Value)
    (table : Table schema.kind Cell) : UnschematizedTable (List Value) :=
  table.map fun row => List.ofFn fun i => encode (schema.kind i) (row i)

end Silmaril.Relational
