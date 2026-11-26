module

public import Silmaril.Relational.Table.Organization.Defs

/-! Whole-table predicates express constraints such as keys. Generated cells are
computed from a typed selection of supplied cells within each row. -/

@[expose] public section

namespace Silmaril.Relational

universe u v w x y

/-- Erasing a constraint certificate is subtype projection. -/
abbrev Constrained (Data : Type u) (valid : Data → Prop) := {data // valid data}

/-- Rows satisfying a local constraint, with the certificate stored once for the table. -/
abbrev CheckedRows {RowId : Type u} {R : Type v} (valid : R → Prop) :=
  Constrained (RowId → R) (fun rows => ∀ id, valid (rows id))

/-- A row has supplied columns and a separate family of generated columns.
Each evaluator receives only the supplied cells selected by its dependency map.
A dependency may occur more than once, and an empty dependency type gives a constant. -/
structure GeneratedColumns {I : Type u} {J : Type v} {Kind : Type w}
    (supplied : I → Kind) (derived : J → Kind) (Cell : Kind → Type x) where
  Dependency : J → Type y
  input : (j : J) → Dependency j → I
  eval : (j : J) → ((d : Dependency j) → Cell (supplied (input j d))) → Cell (derived j)

namespace GeneratedColumns

variable {I : Type u} {J : Type v} {Kind : Type w} {supplied : I → Kind} {derived : J → Kind}
variable {Cell : Kind → Type x}

abbrev Candidate (supplied : I → Kind) (derived : J → Kind) (Cell : Kind → Type x) :=
  Row supplied Cell × Row derived Cell

variable (spec : GeneratedColumns supplied derived Cell)

def evaluate (row : Row supplied Cell) : Row derived Cell :=
  fun j => spec.eval j (fun d => row (spec.input j d))

def Valid (candidate : Candidate supplied derived Cell) : Prop :=
  ∀ j, candidate.2 j = spec.evaluate candidate.1 j

abbrev Checked := Constrained (Candidate supplied derived Cell) spec.Valid

def reconstruct (row : Row supplied Cell) : spec.Checked :=
  ⟨(row, spec.evaluate row), fun _ => rfl⟩

def forgetDerived (checked : spec.Checked) : Row supplied Cell :=
  checked.val.1

/-- Validate externally provided generated values using a decision procedure for the row. -/
def check (candidate : Candidate supplied derived Cell) [Decidable (spec.Valid candidate)] :
    Option spec.Checked :=
  if h : spec.Valid candidate then some ⟨candidate, h⟩ else none

end GeneratedColumns

end Silmaril.Relational
