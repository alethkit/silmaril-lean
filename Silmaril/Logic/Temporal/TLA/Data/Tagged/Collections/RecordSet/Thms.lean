module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.RecordSet

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

/-- Every domain key is the tagged string of a listed label. -/
theorem SetData.mem_recordSetKeys {fields : List (String × SetData.{u})} {key : Value.{u}} :
    (recordSetKeys fields).mem key ↔
      ∃ name, name ∈ fields.map Prod.fst ∧ Value.string name = key :=
  Proofs.Logic.Temporal.TLA.Data.Tagged.RecordSet.mem_recordSetKeys

@[simp] theorem SetData.string_mem_recordSetKeys {fields : List (String × SetData.{u})}
    {name : String} : (recordSetKeys fields).mem (Value.string name) ↔ name ∈ fields.map Prod.fst := by
  simp [mem_recordSetKeys, Value.string_injective.eq_iff]

/-- Membership is graph identity, exact domain, and field-specific range membership. -/
theorem SetData.mem_recordSet {fields : List (String × SetData.{u})} {v : Value.{u}} :
    (recordSet fields).mem v ↔
      ∃ g : Graph.{u}, Value.function g = v ∧ g.domain = recordSetKeys fields ∧
        g.fitsRecordSet fields :=
  Proofs.Logic.Temporal.TLA.Data.Tagged.RecordSet.mem_recordSet

theorem SetData.record_mem_recordSet {fields : List (String × SetData.{u})}
    {body : String → Value.{u}}
    (h : ∀ name bound, (name, bound) ∈ fields → bound.mem (body name)) :
    (recordSet fields).mem (Value.record (fields.map Prod.fst) body) :=
  Proofs.Logic.Temporal.TLA.Data.Tagged.RecordSet.record_mem_recordSet h

/-- A valid empty schema contains exactly the empty graph. -/
@[simp] theorem SetData.mem_recordSet_nil {v : Value.{u}} :
    (recordSet []).mem v ↔ v = Value.function (Graph.ofFn SetData.empty id) :=
  Proofs.Logic.Temporal.TLA.Data.Tagged.RecordSet.mem_recordSet_nil

theorem Value.checkRecordSetFields_duplicate {fields : List (String × Value.{u})}
    (h : ¬ (fields.map Prod.fst).Nodup) :
    checkRecordSetFields fields = .error .duplicateFields := ite_eq_right h

theorem Value.checkRecordSetFields_distinct {fields : List (String × Value.{u})}
    (h : (fields.map Prod.fst).Nodup) :
    checkRecordSetFields fields = decodeRecordSetBounds fields := ite_eq_left h

@[simp] theorem Value.decodeRecordSetBounds_nonSet {name : String} {bound : Value.{u}}
    {rest : List (String × Value.{u})} (h : bound.asSet = none) :
    decodeRecordSetBounds ((name, bound) :: rest) = .error (.nonSetBound name) := by
  simp [decodeRecordSetBounds, h]

theorem Value.checkRecordSetFields_encoded {fields : List (String × SetData.{u})}
    (h : (fields.map Prod.fst).Nodup) :
    checkRecordSetFields (fields.map fun field => (field.1, set field.2)) = .ok fields := by
  rw [checkRecordSetFields_distinct (by simpa [List.map_map, Function.comp_def] using h)]
  exact Proofs.Logic.Temporal.TLA.Data.Tagged.RecordSet.decodeRecordSetBounds_encoded fields

theorem Value.recordSet_valid {fallback : RecordSetFallback.{u}}
    {fields : List (String × Value.{u})} {bounds : List (String × SetData.{u})}
    (h : checkRecordSetFields fields = .ok bounds) :
    recordSet fallback fields = set (SetData.recordSet bounds) := by
  simp [recordSet, h]

theorem Value.recordSet_invalid {fallback : RecordSetFallback.{u}}
    {fields : List (String × Value.{u})} {error : RecordSetError}
    (h : checkRecordSetFields fields = .error error) :
    recordSet fallback fields = fallback error fields := by
  simp [recordSet, h]

@[simp] theorem Value.recordSet_nil (fallback : RecordSetFallback.{u}) :
    recordSet fallback [] = set (SetData.recordSet []) :=
  recordSet_valid (checkRecordSetFields_encoded (fields := []) List.nodup_nil)

end Silmaril.Logic.Temporal.TLA.Data.Tagged
