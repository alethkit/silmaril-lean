module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth

open Silmaril.Languages.Starlark.Lists (Heap Value)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Error Row hashKey storedHash)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Growth

theorem candidates_short (width : Width) (entries : List Row) (hash : UInt32)
    (short : entries.length ≤ 8) :
    orderedCandidates width entries hash =
      (entries.zipIdx.filter fun item => item.1.hash == hash).reverse := by
  have homeBound : (homeRows width entries hash).length ≤ 8 := by
    have filtered := List.length_filter_le (fun item : Row × Nat =>
      width.home item.1.hash == width.home hash) entries.zipIdx
    simp only [List.length_zipIdx] at filtered
    unfold homeRows
    omega
  simp only [orderedCandidates, slotOrder, List.take_of_length_le homeBound,
    List.drop_of_length_le homeBound, overflowOrder, List.append_nil, List.filter_reverse]
  simp only [homeRows, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro item _
  by_cases same : item.1.hash = hash <;> simp [same]

theorem candidates_grow (table : Table) (one : table.width = .one) (hash : UInt32) :
    (table.grow one).candidates hash = table.candidates hash := by
  have short := table.bounded
  rw [one] at short
  change table.entries.length ≤ 8 at short
  simp only [Table.candidates, Table.grow, candidates_short _ _ _ short]

theorem lookup_grow (heap : Heap) (table : Table) (one : table.width = .one) (key : Value) :
    lookupWithHash heap (table.grow one) key = lookupWithHash heap table key := by
  unfold lookupWithHash
  congr 1
  funext word
  change (do
    let hit ← probeTable heap (table.grow one) key (storedHash word)
    pure (storedHash word, hit)) = _
  have same := candidates_grow table one (storedHash word)
  unfold Table.candidates at same
  simp only [probeTable, probeRows, same]

theorem reinserts_two (heap : Heap) (prefixRows remaining : List Row)
    (short : prefixRows.length + remaining.length ≤ 8)
    (original : Reinserts heap .one prefixRows remaining) :
    Reinserts heap .two prefixRows remaining := by
  induction original with
  | done rows => exact .done rows
  | @next earlier row later word hashed stored missed _ _ ih =>
    have bound : earlier.length ≤ 8 := by omega
    have probe : probeRows heap .two earlier row.key row.hash =
        probeRows heap .one earlier row.key row.hash := by
      simp only [probeRows, candidates_short _ _ _ bound]
    refine .next hashed stored (probe.trans missed) (by change earlier.length < 13; omega) (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using short

theorem reinsert_run (heap : Heap) (width : Width) (prefixRows remaining : List Row)
    (steps : Reinserts heap width prefixRows remaining) (bound : prefixRows.length ≤ width.limit) :
    (remaining.foldlM (fun table row =>
      Languages.Starlark.Lists.GoDictionary.Growth.set heap table row.key row.value)
      (⟨width, prefixRows, bound⟩ : Table)).map Table.entries = .ok (prefixRows ++ remaining) := by
  induction steps with
  | done rows => simp [pure, Except.pure, Except.map]
  | @next earlier row later word hashed stored missed room _ ih =>
    let table : Table := ⟨width, earlier, bound⟩
    have read : lookupWithHash heap table row.key = .ok (row.hash, none) := by
      simp [lookupWithHash, hashed, stored, bind, Except.bind, pure, Except.pure, probeTable, table, missed]
    have stays : ¬ (table.width = .one ∧ table.entries.length = 8) := by
      rintro ⟨one, full⟩
      change width = .one at one
      change earlier.length = 8 at full
      simp [one, full, Width.limit] at room
    have hasRoom : table.entries.length < table.width.limit := room
    have write : Languages.Starlark.Lists.GoDictionary.Growth.set heap table row.key row.value =
        .ok (table.insert row room) := by
      unfold Languages.Starlark.Lists.GoDictionary.Growth.set
      rw [read]
      cases row
      simp only [bind, Except.bind, dite_eq_right stays, commit, dite_eq_left hasRoom]
    change Except.map Table.entries ((row :: later).foldlM (fun current item =>
      Languages.Starlark.Lists.GoDictionary.Growth.set heap current item.key item.value) table) = _
    rw [List.foldlM_cons, write]
    change Except.map Table.entries (later.foldlM (fun current item =>
      Languages.Starlark.Lists.GoDictionary.Growth.set heap current item.key item.value) (table.insert row room)) = _
    simpa only [Table.insert, table, List.append_assoc, List.singleton_append] using
      ih (by simpa using Nat.succ_le_of_lt room)

theorem set_hit (heap : Heap) (table : Table) (key value : Value) (hash : UInt32) (hit : Row × Nat)
    (found : lookupWithHash heap table key = .ok (hash, some hit)) :
    set heap table key value = .ok (table.replace hit value) := by
  unfold Languages.Starlark.Lists.GoDictionary.Growth.set
  rw [found]
  rfl

theorem set_first_grow (heap : Heap) (table : Table) (key value : Value) (hash : UInt32)
    (one : table.width = .one) (full : table.entries.length = 8)
    (missing : lookupWithHash heap table key = .ok (hash, none)) :
    set heap table key value = .ok ((table.grow one).insert ⟨hash, key, value⟩
      (by change table.entries.length < 13; omega)) := by
  have again := (lookup_grow heap table one key).trans missing
  have probed : probeTable heap (table.grow one) key hash = .ok none := by
    cases hashed : hashKey heap key with
    | error error => simp [lookupWithHash, hashed, bind, Except.bind] at again
    | ok word =>
      cases checked : probeTable heap (table.grow one) key (storedHash word) with
      | error error => simp [lookupWithHash, hashed, checked, bind, Except.bind] at again
      | ok hit =>
        simp [lookupWithHash, hashed, checked, bind, Except.bind, pure, Except.pure] at again
        rw [← again.1, checked, again.2]
  unfold Languages.Starlark.Lists.GoDictionary.Growth.set
  rw [missing]
  change (if h : table.width = .one ∧ table.entries.length = 8 then
    (do commit (table.grow h.1) ⟨hash, key, value⟩ (← probeTable heap (table.grow h.1) key hash))
    else commit table ⟨hash, key, value⟩ none) = _
  rw [dite_eq_left ⟨one, full⟩, probed]
  change commit (table.grow one) ⟨hash, key, value⟩ none = _
  simp only [commit, dite_eq_left (show (table.grow one).entries.length < (table.grow one).width.limit by
    change table.entries.length < 13
    omega)]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth
