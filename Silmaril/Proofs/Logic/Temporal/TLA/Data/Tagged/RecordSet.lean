module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.RecordSet

open Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

private theorem rangeBound_mem {fields : List (String × SetData.{u})}
    {field : String × SetData.{u}} {x : Value.{u}} (h : field ∈ fields) (hx : field.2.mem x) :
    x.code ∈ fields.foldr (fun field acc => field.2.codes ∪ acc) ∅ := by
  induction fields with
  | nil => cases h
  | cons front rest ih =>
    change x.code ∈ front.2.codes ∪ rest.foldr (fun field acc => field.2.codes ∪ acc) ∅
    rcases List.mem_cons.mp h with rfl | hr
    · exact ZFSet.mem_union.mpr (.inl hx)
    · exact ZFSet.mem_union.mpr (.inr (ih hr))

theorem mem_recordSetKeys {fields : List (String × SetData.{u})} {key : Value.{u}} :
    (SetData.recordSetKeys fields).mem key ↔
      ∃ name, name ∈ fields.map Prod.fst ∧ Value.string name = key := by
  rw [SetData.recordSetKeys, SetData.mem_enum, List.mem_map]

theorem mem_recordSet {fields : List (String × SetData.{u})} {v : Value.{u}} :
    (SetData.recordSet fields).mem v ↔
      ∃ g : Graph.{u}, Value.function g = v ∧
        g.domain = SetData.recordSetKeys fields ∧ g.fitsRecordSet fields := by
  rw [SetData.recordSet, SetData.mem_sep, SetData.mem_functionSet]
  constructor
  · rintro ⟨⟨g, hg, hd, _⟩, ⟨h, hh, hf⟩⟩
    exact ⟨g, hg, hd, Value.function_injective (hh.trans hg.symm) ▸ hf⟩
  · rintro ⟨g, hg, hd, hf⟩
    refine ⟨⟨g, hg, hd, ?_⟩, ⟨g, hg, hf⟩⟩
    intro x y hxy
    have hx : (SetData.recordSetKeys fields).mem x := hd ▸ Graph.mem_domain.mpr ⟨y, hxy⟩
    obtain ⟨name, hname, hkey⟩ := mem_recordSetKeys.mp hx
    obtain ⟨⟨name, bound⟩, hfield, rfl⟩ := List.mem_map.mp hname
    subst x
    obtain ⟨value, hlookup, hmem⟩ := hf name bound hfield
    have he := Option.some.inj ((Graph.lookup_eq_some.mpr hxy).symm.trans hlookup)
    exact rangeBound_mem hfield (he.symm ▸ hmem)

theorem record_mem_recordSet {fields : List (String × SetData.{u})} {body : String → Value.{u}}
    (h : ∀ name bound, (name, bound) ∈ fields → bound.mem (body name)) :
    (SetData.recordSet fields).mem (Value.record (fields.map Prod.fst) body) := by
  refine mem_recordSet.mpr ⟨Graph.record (fields.map Prod.fst) body, rfl, ?_, ?_⟩
  · exact Graph.domain_record _ _
  · intro name bound hfield
    exact ⟨body name, Graph.lookup_record body (List.mem_map_of_mem hfield), h name bound hfield⟩

theorem mem_recordSet_nil {v : Value.{u}} :
    (SetData.recordSet []).mem v ↔ v = Value.function (Graph.ofFn SetData.empty id) := by
  have hkeys : SetData.recordSetKeys ([] : List (String × SetData.{u})) = SetData.empty := by
    apply SetData.ext
    intro key
    rw [SetData.recordSetKeys, SetData.mem_enum]
    simp [SetData.empty, SetData.mem]
  rw [mem_recordSet, hkeys]
  constructor
  · rintro ⟨g, rfl, hdom, _⟩
    congr 1
    apply Graph.ext_of_domain_lookup (hdom.trans (Graph.domain_ofFn _ _).symm)
    intro x hx
    simp [hdom, SetData.empty, SetData.mem] at hx
  · rintro rfl
    exact ⟨_, rfl, Graph.domain_ofFn _ _, fun _ _ h => (List.not_mem_nil h).elim⟩

theorem decodeRecordSetBounds_encoded (fields : List (String × SetData.{u})) :
    Value.decodeRecordSetBounds (fields.map fun field => (field.1, Value.set field.2)) =
      .ok fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    obtain ⟨name, bound⟩ := field
    simp [Value.decodeRecordSetBounds, ih, Except.map]

end Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.RecordSet
