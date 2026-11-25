module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Defs

/-! # Mathematical record sets over the tagged graph representation -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

/-- The exact domain of a record in the schema, using tagged string keys. -/
noncomputable def SetData.recordSetKeys (fields : List (String × SetData.{u})) : SetData.{u} :=
  enum ((fields.map Prod.fst).map Value.string)

/-- Each listed field has a graph value in its own bound. -/
def Graph.fitsRecordSet (g : Graph.{u}) (fields : List (String × SetData.{u})) : Prop :=
  ∀ name bound, (name, bound) ∈ fields →
    ∃ value, g.lookup (Value.string name) = some value ∧ bound.mem value

/-- Graphs on the exact key set, with one range restriction for every entry.
Repeated labels in this typed operation impose all of their restrictions. -/
noncomputable def SetData.recordSet (fields : List (String × SetData.{u})) : SetData.{u} :=
  let bound : SetData := ⟨fields.foldr (fun field acc => field.2.codes ∪ acc) ∅⟩
  ((recordSetKeys fields).functionSet bound).sep
    (fun value => ∃ g : Graph.{u}, Value.function g = value ∧ g.fitsRecordSet fields)

/-- A malformed value-level schema. Duplicate labels take precedence over bad bounds. -/
inductive RecordSetError where
  | duplicateFields
  | nonSetBound (name : String)
  deriving DecidableEq, Repr

/-- The caller fixes this policy across evaluations. It sees the error and original operands. -/
abbrev RecordSetFallback :=
  RecordSetError → List (String × Value.{u}) → Value.{u}

/-- Decode all bounds in order. The first failed bound supplies the diagnostic. -/
noncomputable def Value.decodeRecordSetBounds :
    List (String × Value.{u}) → Except RecordSetError (List (String × SetData.{u}))
  | [] => .ok []
  | (name, value) :: rest =>
    match value.asSet with
    | none => .error (.nonSetBound name)
    | some bound => (decodeRecordSetBounds rest).map ((name, bound) :: ·)

/-- Validate distinct labels before decoding the field bounds. -/
noncomputable def Value.checkRecordSetFields (fields : List (String × Value.{u})) :
    Except RecordSetError (List (String × SetData.{u})) :=
  if (fields.map Prod.fst).Nodup then decodeRecordSetBounds fields else .error .duplicateFields

/-- The record-set operation on values. A malformed schema is evaluated by the fixed policy. -/
noncomputable def Value.recordSet (fallback : RecordSetFallback.{u})
    (fields : List (String × Value.{u})) : Value.{u} :=
  match checkRecordSetFields fields with
  | .ok bounds => set (SetData.recordSet bounds)
  | .error error => fallback error fields

end Silmaril.Logic.Temporal.TLA.Data.Tagged
