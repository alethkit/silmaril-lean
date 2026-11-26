module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Slots

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth

open Silmaril.Languages.Starlark.Lists.GoDictionary (Error Row hashKey storedHash)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Growth
open Silmaril.Languages.Starlark.Lists (Heap Value)

theorem occupied_slots {α : Type} (entries : List α) :
    (physicalChain entries).filterMap id = slotOrder entries := by
  have empty : (id : Option α → Option α) none = none := rfl
  have suffix (later : List α) (n : Nat) :
      ((List.replicate n none ++ later.map some).filterMap id) = later := by
    simp [List.filterMap_replicate_of_none empty, List.filterMap_map, Function.comp_def]
  rw [physicalChain, slotOrder, List.filterMap_append, primarySlots, suffix]
  cases h : entries.drop 8 with
  | nil => rfl
  | cons first later => simp [overflowSlots, overflowOrder]

theorem slot_order_perm {α : Type} (entries : List α) :
    (slotOrder entries).Perm entries := by
  have overflow (rows : List α) : (overflowOrder rows).Perm rows := by
    cases rows with
    | nil => exact .nil
    | cons first later => exact .cons first (List.reverse_perm later)
  simpa only [slotOrder, List.take_append_drop] using
    (List.reverse_perm (entries.take 8)).append
      (overflow (entries.drop 8))

theorem chain_size {α : Type} (entries : List α) (bound : entries.length ≤ 16) :
    (physicalChain entries).length = if entries.length ≤ 8 then 8 else 16 := by
  have primary : (primarySlots entries).length = 8 := by
    simp only [primarySlots, List.length_append, List.length_replicate, List.length_map,
      List.length_reverse, List.length_take]
    omega
  rw [physicalChain, List.length_append, primary]
  have dropLength := List.length_drop (l := entries) (i := 8)
  cases h : entries.drop 8 with
  | nil =>
    rw [h, List.length_nil] at dropLength
    simp [overflowSlots, show entries.length ≤ 8 by omega]
  | cons first later =>
    rw [h, List.length_cons] at dropLength
    simp only [overflowSlots, List.length_cons, List.length_append, List.length_replicate,
      List.length_map, List.length_reverse, ite_eq_right (show ¬ entries.length ≤ 8 by omega)]
    omega

theorem candidates_slots (table : Table) (hash : UInt32) :
    table.candidates hash = (table.slots hash).filterMap (fun cell =>
      cell.filter fun item => item.1.hash == hash) := by
  rw [Table.candidates, orderedCandidates, Table.slots, Table.homeEntries, ← occupied_slots, List.filter_filterMap]
  rfl

theorem home_length_le (table : Table) (hash : UInt32) :
    (table.homeEntries hash).length ≤ table.entries.length := by
  simpa [Table.homeEntries, homeRows] using
    List.length_filter_le (fun item : Row × Nat =>
      table.width.home item.1.hash == table.width.home hash) table.entries.zipIdx

theorem slots_wellFormed (table : Table) (hash : UInt32) :
    ((table.slots hash).filterMap id).Perm (table.homeEntries hash) ∧
    (table.slots hash).length = (if (table.homeEntries hash).length ≤ 8 then 8 else 16) := by
  have home := home_length_le table hash
  have bound := table.bounded
  have fits : table.width.limit ≤ 16 := by cases table.width <;> decide
  exact ⟨by rw [Table.slots, occupied_slots]; exact slot_order_perm _,
    chain_size _ (by omega)⟩

theorem home_append (table : Table) (row : Row) (room : table.entries.length < table.width.limit)
    (hash : UInt32) :
    (table.insert row room).homeEntries hash = table.homeEntries hash ++
      (if table.width.home row.hash = table.width.home hash then [(row, table.entries.length)] else []) := by
  by_cases same : table.width.home row.hash = table.width.home hash <;>
    simp [Table.insert, Table.homeEntries, homeRows, List.zipIdx_append, same]

private theorem fill_suffix {α : Type} (entries : List α) (row : α) (slot : Nat) :
    (List.replicate (slot + 1) none ++ entries.map some).set slot (some row) =
      List.replicate slot none ++ some row :: entries.map some := by
  rw [List.replicate_succ', List.append_assoc, List.set_append_right (h := by simp)]
  simp

theorem append_primary {α : Type} (entries : List α) (row : α) (room : entries.length < 8) :
    physicalChain (entries ++ [row]) =
      (physicalChain entries).set (7 - entries.length) (some row) := by
  have before : entries.length ≤ 8 := by omega
  have after : (entries ++ [row]).length ≤ 8 := by simp; omega
  have vacant : 8 - entries.length = (7 - entries.length) + 1 := by omega
  have remaining : 8 - (entries.length + 1) = 7 - entries.length := by omega
  simp only [physicalChain, primarySlots, List.take_of_length_le before, List.take_of_length_le after,
    List.drop_of_length_le before, List.drop_of_length_le after, overflowSlots, List.append_nil,
    List.length_append, List.length_singleton, Nat.add_one, remaining, vacant, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.map_cons]
  exact (fill_suffix entries.reverse row (7 - entries.length)).symm

theorem append_first_overflow {α : Type} (entries : List α) (row : α) (full : entries.length = 8) :
    physicalChain (entries ++ [row]) = physicalChain entries ++ (some row :: List.replicate 7 none) := by
  have takeRows := List.take_append_of_le_length (l₁ := entries) (l₂ := [row]) (i := 8) (by omega)
  have suffix := List.drop_append_of_le_length (l₁ := entries) (l₂ := [row]) (i := 8) (by omega)
  rw [physicalChain, physicalChain, primarySlots, primarySlots, takeRows, suffix]
  simp [full, List.drop_of_length_le (show entries.length ≤ 8 by omega), overflowSlots]

theorem append_overflow {α : Type} (entries : List α) (row : α)
    (overflow : 8 < entries.length) (room : entries.length < 16) :
    physicalChain (entries ++ [row]) =
      (physicalChain entries).set (24 - entries.length) (some row) := by
  have takeRows := List.take_append_of_le_length (l₁ := entries) (l₂ := [row]) (i := 8) (by omega)
  have suffix := List.drop_append_of_le_length (l₁ := entries) (l₂ := [row]) (i := 8) (by omega)
  have size : (primarySlots entries).length = 8 := by
    simp [primarySlots, List.length_take, Nat.min_eq_left (show 8 ≤ entries.length by omega)]
  have length := List.length_drop (l := entries) (i := 8)
  cases h : entries.drop 8 with
  | nil => simp [h] at length; omega
  | cons first later =>
    rw [h, List.length_cons] at length
    have vacant : 7 - later.length = (6 - later.length) + 1 := by omega
    have remaining : 7 - (later.length + 1) = 6 - later.length := by omega
    have index : 24 - entries.length - 8 = (6 - later.length) + 1 := by omega
    rw [physicalChain, physicalChain, List.set_append_right (h := by omega), size, index]
    simp only [primarySlots, takeRows, suffix, h, List.cons_append, overflowSlots, List.length_append,
      List.length_singleton, remaining, vacant, List.reverse_append, List.reverse_singleton,
      List.nil_append, List.map_cons, List.set_cons_succ]
    rw [fill_suffix]

theorem lookup_hit_row (heap : Heap) (table : Table) (key : Value) (hash : UInt32)
    (hit : Row × Nat) (found : lookupWithHash heap table key = .ok (hash, some hit)) :
    table.entries[hit.2]? = some hit.1 := by
  let test := fun (candidate : Row × Nat) =>
    Languages.Starlark.Lists.Comparison.equalAt heap
      Languages.Starlark.Lists.Comparison.defaultDepth key candidate.1.key
  cases digest : hashKey heap key with
  | error error => simp [lookupWithHash, digest, bind, Except.bind] at found
  | ok word =>
    let candidates := table.candidates (storedHash word)
    cases ran : Languages.Starlark.Lists.Comparison.probe test candidates with
    | error error =>
      dsimp [test, candidates, Table.candidates] at ran
      simp [lookupWithHash, probeTable, probeRows, digest, ran,
        bind, Except.bind, Except.mapError] at found
    | ok picked =>
      have data : (storedHash word, picked) = (hash, some hit) := by
        have checked := ran
        dsimp [test, candidates, Table.candidates] at checked
        simpa [lookupWithHash, probeTable, probeRows, digest, checked,
          bind, Except.bind, Except.mapError, pure, Except.pure] using found
      rw [(Prod.mk.inj data).2] at ran
      have mem := GoDictionary.probe_hit_mem test candidates hit ran
      have home : hit ∈ table.homeEntries (storedHash word) :=
        (slot_order_perm _).mem_iff.mp (List.mem_filter.mp mem).1
      rcases hit with ⟨row, index⟩
      exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp home).1

theorem replace_keeps_keys (table : Table) (hit : Row × Nat) (value : Value)
    (present : table.entries[hit.2]? = some hit.1) :
    (table.replace hit value).entries.map (fun row => (row.hash, row.key)) =
      table.entries.map (fun row => (row.hash, row.key)) := by
  obtain ⟨valid, same⟩ := List.getElem?_eq_some_iff.mp present
  have keyAt : (table.entries.map (fun row => (row.hash, row.key)))[hit.2]'(by simpa using valid) =
      (hit.1.hash, hit.1.key) := by simp [same]
  simp only [Table.replace, List.map_set]
  rw [← keyAt, List.set_getElem_self]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth
