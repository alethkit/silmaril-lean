module

public import Silmaril.Relational.Table.Defs
import Silmaril.Proofs.Relational.Table.Organization

/-! Public theorems for schemas, list and indexed tables, and generated columns. -/

@[expose] public section

namespace Silmaril.Relational

universe u v w x y

namespace ColumnMap

variable {I : Type u} {J : Type v} {K : Type w} {Label : Type x} {Kind : Type y}
variable {a : I → Label} {b : J → Label} {c : K → Label}
variable {Cell : Kind → Type*} (kind : Label → Kind)

@[simp] theorem pullRow_id (row : Row (kind ∘ a) Cell) :
    (ColumnMap.id a).pullRow kind row = row := rfl

theorem pullRow_comp (f : ColumnMap a b) (g : ColumnMap b c)
    (row : Row (kind ∘ c) Cell) :
    (f.comp g).pullRow kind row = f.pullRow kind (g.pullRow kind row) := by
  funext i
  simp only [ColumnMap.pullRow, ColumnMap.comp, cast_cast]

end ColumnMap

namespace AlignedColumns

variable {I : Type u} {Kind : Type v} {kind : I → Kind} {Cell : Kind → Type w}

@[simp] theorem toRows_ofRows (rows : Table kind Cell) : (ofRows rows).toRows = rows :=
  Proofs.Relational.Table.toRows_ofRows rows

@[simp] theorem ofRows_toRows (columns : AlignedColumns kind Cell) : ofRows columns.toRows = columns :=
  Proofs.Relational.Table.ofRows_toRows columns

@[simp] theorem length_toRows (columns : AlignedColumns kind Cell) :
    columns.toRows.length = columns.rowCount := List.length_ofFn

/-- This transposition fixes every list position. A zero-column table keeps its row count. -/
def rowsEquiv : Table kind Cell ≃ AlignedColumns kind Cell :=
  ⟨ofRows, toRows, toRows_ofRows, ofRows_toRows⟩

end AlignedColumns

namespace PositionalSchema

variable {Kind : Type u} {Cell : Kind → Type v} {Value : Type w}
variable (schema : PositionalSchema Kind) (encode : (k : Kind) → Cell k → Value)

@[simp] theorem length_eraseTable (table : Table schema.kind Cell) :
    (schema.eraseTable encode table).length = table.length := List.length_map _

theorem length_row_of_mem_eraseTable (table : Table schema.kind Cell) {row : List Value}
    (mem : row ∈ schema.eraseTable encode table) : row.length = schema.width := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp mem
  exact List.length_ofFn

end PositionalSchema

/-- Move the proof of a row-local constraint between the row and table levels. -/
def checkedRowsEquiv {RowId : Type u} {R : Type v} (valid : R → Prop) :
    CheckedRows (RowId := RowId) valid ≃ (RowId → Constrained R valid) where
  toFun rows id := ⟨rows.val id, rows.property id⟩
  invFun rows := ⟨fun id => (rows id).val, fun id => (rows id).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Attach a constraint to an entire packed entry or to its schema-indexed payload. -/
def constrainedSigmaEquiv {Schema : Type u} {Data : Schema → Type v}
    (valid : (schema : Schema) → Data schema → Prop) :
    (Σ schema, Constrained (Data schema) (valid schema)) ≃
      Constrained (Sigma Data) (fun entry => valid entry.fst entry.snd) where
  toFun entry := ⟨⟨entry.fst, entry.snd.val⟩, entry.snd.property⟩
  invFun entry := ⟨entry.val.fst, ⟨entry.val.snd, entry.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace GeneratedColumns

variable {I : Type u} {J : Type v} {Kind : Type w} {supplied : I → Kind} {derived : J → Kind}
variable {Cell : Kind → Type x} (spec : GeneratedColumns supplied derived Cell)

@[simp] theorem forgetDerived_reconstruct (row : Row supplied Cell) :
    spec.forgetDerived (spec.reconstruct row) = row := rfl

@[simp] theorem reconstruct_forgetDerived (checked : spec.Checked) :
    spec.reconstruct (spec.forgetDerived checked) = checked :=
  Subtype.ext (Prod.ext rfl (funext checked.property).symm)

/-- A checked materialized row is determined by its supplied cells. -/
def checkedEquivSupplied : spec.Checked ≃ Row supplied Cell :=
  ⟨spec.forgetDerived, spec.reconstruct, spec.reconstruct_forgetDerived, spec.forgetDerived_reconstruct⟩

@[simp] theorem check_eq_some_iff (candidate : Candidate supplied derived Cell)
    [Decidable (spec.Valid candidate)] (checked : spec.Checked) :
    spec.check candidate = some checked ↔ candidate = checked.val := by
  by_cases valid : spec.Valid candidate <;> simp [check, valid, Subtype.ext_iff]
  exact fun h => valid (h ▸ checked.property)

@[simp] theorem check_eq_none_iff (candidate : Candidate supplied derived Cell)
    [Decidable (spec.Valid candidate)] :
    spec.check candidate = none ↔ ¬ spec.Valid candidate := by
  by_cases valid : spec.Valid candidate <;> simp [check, valid]

end GeneratedColumns

end Silmaril.Relational
