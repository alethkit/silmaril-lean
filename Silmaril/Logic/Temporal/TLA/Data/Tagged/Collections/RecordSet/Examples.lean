module

import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Thms

/-! Checked cases for the record-set operation on tagged values. -/

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

private noncomputable def fields (participants : SetData.{u}) : List (String × SetData.{u}) :=
  [("request", participants.functionSet SetData.booleans), ("alive", SetData.booleans)]

private noncomputable def body (participants : SetData.{u}) (name : String) : Value.{u} :=
  if name = "request" then .function (Graph.ofFn participants fun _ => .boolean false)
  else .boolean true

private theorem request_mem (participants : SetData.{u}) :
    (participants.functionSet SetData.booleans).mem (body participants "request") := by
  simp only [body, ite_true]
  refine SetData.mem_functionSet.mpr ⟨_, rfl, Graph.domain_ofFn _ _, ?_⟩
  intro _ _ h
  exact SetData.mem_booleans.mpr ⟨false, (Graph.relates_ofFn.mp h).2⟩

private theorem member (participants : SetData.{u}) :
    (SetData.recordSet (fields participants)).mem
      (Value.record ((fields participants).map Prod.fst) (body participants)) := by
  apply SetData.record_mem_recordSet
  intro name bound h
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h <;> cases h
  · exact request_mem participants
  · exact SetData.mem_booleans.mpr ⟨true, by simp [body]⟩

example : (SetData.recordSet (fields SetData.empty)).mem
    (Value.record ((fields SetData.empty).map Prod.fst) (body SetData.empty : String → Value.{0})) :=
  member SetData.empty

example : (SetData.recordSet (fields SetData.integers)).mem
    (Value.record ((fields SetData.integers).map Prod.fst) (body SetData.integers : String → Value.{0})) :=
  member SetData.integers

example (participants : SetData.{u}) {g : Graph.{u}}
    (h : (SetData.recordSet (fields participants)).mem (Value.function g)) :
    g.domain.mem (Value.string "request") ∧ ¬ g.domain.mem (Value.string "Request") := by
  obtain ⟨graph, heq, hd, _⟩ := SetData.mem_recordSet.mp h
  cases Value.function_injective heq
  simp [hd, fields]

/-- Every matching record has a graph-valued field on exactly the supplied participant set. -/
example (participants : SetData.{u}) {g : Graph.{u}}
    (h : (SetData.recordSet (fields participants)).mem (Value.function g)) :
    ∃ f : Graph.{u}, g.lookup (Value.string "request") = some (Value.function f) ∧
      f.domain = participants := by
  obtain ⟨graph, heq, _, hfields⟩ := SetData.mem_recordSet.mp h
  cases Value.function_injective heq
  obtain ⟨w, hw, hmem⟩ :=
    hfields "request" (participants.functionSet SetData.booleans) (by simp [fields])
  obtain ⟨f, rfl, hd, _⟩ := SetData.mem_functionSet.mp hmem
  exact ⟨f, hw, hd⟩

example (v : Value.{u}) : ¬ (SetData.recordSet [("missing", SetData.empty)]).mem v := by
  intro h
  obtain ⟨g, _, _, hfields⟩ := SetData.mem_recordSet.mp h
  obtain ⟨w, _, hw⟩ := hfields "missing" SetData.empty (by simp)
  simp [SetData.empty, SetData.mem] at hw

private def fallback : RecordSetFallback.{u}
  | .duplicateFields, _ => .boolean false
  | .nonSetBound _, _ => .boolean true

example :
    Value.recordSet fallback [("x", Value.boolean.{u} false), ("x", .set .booleans)] =
      .boolean false :=
  Value.recordSet_invalid (Value.checkRecordSetFields_duplicate (by simp))

example :
    Value.recordSet fallback [("ok", .set .booleans), ("x", Value.boolean.{u} false)] =
      .boolean true := by
  apply Value.recordSet_invalid (error := .nonSetBound "x")
  simp [Value.checkRecordSetFields, Value.decodeRecordSetBounds, Except.map]

example (v : Value.{u}) :
    v.mem (Value.recordSet fallback []) ↔ v = Value.function (Graph.ofFn SetData.empty id) := by
  simp

end Silmaril.Logic.Temporal.TLA.Data.Tagged
