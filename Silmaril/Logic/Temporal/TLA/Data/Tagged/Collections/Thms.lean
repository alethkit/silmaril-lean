module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Functions.Thms
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Scalars.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.Collections

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

theorem Value.character_injective : Function.Injective character.{u} :=
  fun _ _ h => Char.toNat_inj.mp (natCode_injective (tagged_inj.mp h).2)

theorem Value.function_ne_integer (g : Graph.{u}) (n : Int) : function g ≠ integer n :=
  fun h => Kind.noConfusion (tagged_inj.mp h).1

theorem Value.function_ne_boolean (g : Graph.{u}) (b : Bool) : function g ≠ boolean b :=
  fun h => Kind.noConfusion (tagged_inj.mp h).1

@[simp] theorem Value.asInt_function (g : Graph.{u}) : (function g).asInt = none :=
  decode_eq_none (fun ⟨n, h⟩ => function_ne_integer g n h.symm)

@[simp] theorem Value.asBool_function (g : Graph.{u}) : (function g).asBool = none :=
  decode_eq_none (fun ⟨b, h⟩ => function_ne_boolean g b h.symm)

@[simp] theorem Value.asFunction_integer (n : Int) : (Value.integer.{u} n).asFunction = none :=
  decode_eq_none (fun ⟨g, h⟩ => function_ne_integer g n h)

@[simp] theorem Value.asFunction_boolean (b : Bool) : (Value.boolean.{u} b).asFunction = none :=
  decode_eq_none (fun ⟨g, h⟩ => function_ne_boolean g b h)

@[simp] theorem Graph.domain_tuple (xs : List Value.{u}) :
    (tuple xs).domain = SetData.intRange 1 xs.length :=
  Proofs.domain_tuple xs

theorem Graph.lookup_tuple (xs : List Value.{u}) {i : Nat} (hi : i < xs.length) :
    (tuple xs).lookup (.integer ((↑(i + 1) : Int))) = some xs[i] :=
  Proofs.lookup_tuple xs hi

theorem Graph.tuple_injective : Function.Injective tuple.{u} :=
  Proofs.tuple_injective

theorem Value.string_injective : Function.Injective string.{u} := by
  intro s t h
  have hm := Graph.tuple_injective (function_injective h)
  exact String.ext ((List.map_inj_right (fun _ _ h => character_injective h)).mp hm)

@[simp] theorem Value.string_empty : string.{u} "" = tuple [] := rfl

@[simp] theorem Graph.domain_record (fields : List String) (body : String → Value.{u}) :
    (record fields body).domain = SetData.enum (fields.map Value.string) :=
  domain_ofFn _ _

theorem Graph.lookup_record {fields : List String} (body : String → Value.{u})
    {name : String} (hn : name ∈ fields) : (record fields body).lookup (.string name) = some (body name) := by
  have hd : decode Value.string.{u} (.string name) = some name :=
    (decode_eq_some Value.string_injective).mpr rfl
  rw [record, lookup_ofFn ((SetData.mem_enum _ _).mpr (List.mem_map_of_mem hn))]
  simp [hd]

end Silmaril.Logic.Temporal.TLA.Data.Tagged
