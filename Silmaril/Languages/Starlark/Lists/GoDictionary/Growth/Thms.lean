module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth.Layout
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth.Rehash

public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Growth

/-- Each indexed home row occupies exactly one slot. The overflow block is
present exactly when the primary bucket cannot hold the home rows. -/
theorem slots_wellFormed (table : Table) (hash : UInt32) :
    ((table.slots hash).filterMap id).Perm (table.homeEntries hash) ∧
    (table.slots hash).length = (if (table.homeEntries hash).length ≤ 8 then 8 else 16) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.slots_wellFormed table hash

/-- Appending a row changes only its own home chain. -/
theorem home_append (table : Table) (row : Row) (room : table.entries.length < table.width.limit)
    (hash : UInt32) :
    (table.insert row room).homeEntries hash = table.homeEntries hash ++
      (if table.width.home row.hash = table.width.home hash then [(row, table.entries.length)] else []) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.home_append table row room hash

theorem append_primary {α : Type} (entries : List α) (row : α) (room : entries.length < 8) :
    physicalChain (entries ++ [row]) =
      (physicalChain entries).set (7 - entries.length) (some row) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.append_primary entries row room

theorem append_first_overflow {α : Type} (entries : List α) (row : α) (full : entries.length = 8) :
    physicalChain (entries ++ [row]) = physicalChain entries ++ (some row :: List.replicate 7 none) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.append_first_overflow entries row full

theorem append_overflow {α : Type} (entries : List α) (row : α)
    (overflow : 8 < entries.length) (room : entries.length < 16) :
    physicalChain (entries ++ [row]) =
      (physicalChain entries).set (24 - entries.length) (some row) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.append_overflow entries row overflow room

/-- Lookup visits precisely the occupied slots with the full stored hash, in
primary then overflow order. -/
theorem candidates_slots (table : Table) (hash : UInt32) :
    table.candidates hash = (table.slots hash).filterMap (fun cell =>
      cell.filter fun item => item.1.hash == hash) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.candidates_slots table hash

/-- Before any home can have overflow, a probe sees exactly the reverse
insertion order of its full-hash cohort, irrespective of the home mask. -/
theorem candidates_short (width : Width) (entries : List Row) (hash : UInt32)
    (short : entries.length ≤ 8) :
    orderedCandidates width entries hash =
      (entries.zipIdx.filter fun item => item.1.hash == hash).reverse :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.candidates_short width entries hash short

theorem candidates_grow (table : Table) (one : table.width = .one) (hash : UInt32) :
    (table.grow one).candidates hash = table.candidates hash :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.candidates_grow table one hash

/-- The split alone preserves even a reached raw lookup error. -/
theorem lookup_grow (heap : Heap) (table : Table) (one : table.width = .one) (key : Value) :
    lookupWithHash heap (table.grow one) key = lookupWithHash heap table key :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.lookup_grow heap table one key

theorem grow_keeps_entries (table : Table) (one : table.width = .one) :
    (table.grow one).entries = table.entries := rfl

/-- Every successful chronological replay of at most eight stable-hash rows
also succeeds at the wider mask, with the same original rows. -/
theorem reinserts_two (heap : Heap) (prefixRows remaining : List Row)
    (short : prefixRows.length + remaining.length ≤ 8)
    (original : Reinserts heap .one prefixRows remaining) :
    Reinserts heap .two prefixRows remaining :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.reinserts_two heap prefixRows remaining short original

/-- The replay rules give the final chronological rows of actual insertions. -/
theorem reinsert_run (heap : Heap) (width : Width) (prefixRows remaining : List Row)
    (steps : Reinserts heap width prefixRows remaining) (bound : prefixRows.length ≤ width.limit) :
    (remaining.foldlM (fun table row => set heap table row.key row.value)
      (⟨width, prefixRows, bound⟩ : Table)).map Table.entries = .ok (prefixRows ++ remaining) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.reinsert_run heap width prefixRows remaining steps bound

theorem lookup_hit_row (heap : Heap) (table : Table) (key : Value) (hash : UInt32)
    (hit : Row × Nat) (found : lookupWithHash heap table key = .ok (hash, some hit)) :
    table.entries[hit.2]? = some hit.1 :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.lookup_hit_row heap table key hash hit found

theorem replace_keeps_keys (table : Table) (hit : Row × Nat) (value : Value)
    (present : table.entries[hit.2]? = some hit.1) :
    (table.replace hit value).entries.map (fun row => (row.hash, row.key)) =
      table.entries.map (fun row => (row.hash, row.key)) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.replace_keeps_keys table hit value present

theorem set_hit (heap : Heap) (table : Table) (key value : Value) (hash : UInt32) (hit : Row × Nat)
    (found : lookupWithHash heap table key = .ok (hash, some hit)) :
    set heap table key value = .ok (table.replace hit value) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.set_hit heap table key value hash hit found

theorem set_first_grow (heap : Heap) (table : Table) (key value : Value) (hash : UInt32)
    (one : table.width = .one) (full : table.entries.length = 8)
    (missing : lookupWithHash heap table key = .ok (hash, none)) :
    set heap table key value = .ok ((table.grow one).insert ⟨hash, key, value⟩
      (by change table.entries.length < 13; omega)) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.set_first_grow heap table key value hash one full missing

end Silmaril.Languages.Starlark.Lists.GoDictionary.Growth
