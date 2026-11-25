module

public import Silmaril.Formats.Sqlite.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.Shell.Seek.Thms

public section

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile

namespace Silmaril.Proofs.Formats.Sqlite.Shell.Seek.Snapshot

private theorem lookup_rows (key : Int64) (rows : List Row) :
    BTree.Abstract.lookupList key.toInt (rows.map Row.entry) =
      (rows.find? fun row => row.id == key).map fun row => [.integer key, .integer row.amount] := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases same : row.id = key
    · simp [Row.entry, BTree.Abstract.lookupList, same]
    · have other : row.id.toInt ≠ key.toInt := fun equality =>
        same (Int64.toInt_inj.mp equality)
      simp [Row.entry, BTree.Abstract.lookupList, same, other, ih]

private theorem same_id (snapshot : Snapshot) {first second : Row}
    (left : first ∈ snapshot.rows) (right : second ∈ snapshot.rows)
    (same : first.id = second.id) : first = second := by
  obtain ⟨i, iBound, rfl⟩ := List.mem_iff_getElem.mp left
  obtain ⟨j, jBound, rfl⟩ := List.mem_iff_getElem.mp right
  have iMapped : i < (snapshot.rows.map Row.id).length := by simpa using iBound
  have jMapped : j < (snapshot.rows.map Row.id).length := by simpa using jBound
  have idEqual : (snapshot.rows.map Row.id)[i] = (snapshot.rows.map Row.id)[j] := by
    simpa only [List.getElem_map] using same
  have indexEqual := snapshot.unique.eq_of_getElem_eq iMapped jMapped idEqual
  subst j
  rfl

private theorem find_ordered (snapshot : Snapshot) (key : Int64) :
    (snapshot.orderedRows.find? fun row => row.id == key) =
      (snapshot.rows.find? fun row => row.id == key) := by
  have perm : snapshot.orderedRows.Perm snapshot.rows := List.mergeSort_perm _ _
  cases sorted : snapshot.orderedRows.find? (fun row => row.id == key) with
  | none =>
    exact (List.find?_eq_none.mpr fun row h =>
      List.find?_eq_none.mp sorted row (perm.mem_iff.mpr h)).symm
  | some row =>
    have rowMem := perm.mem_iff.mp (List.mem_of_find?_eq_some sorted)
    have rowMatches := List.find?_some sorted
    have rowKey : row.id = key := beq_iff_eq.mp rowMatches
    cases source : snapshot.rows.find? (fun row => row.id == key) with
    | none =>
      exact False.elim ((List.find?_eq_none.mp source row rowMem) (beq_iff_eq.mpr rowKey))
    | some other =>
      have otherMatches := List.find?_some source
      have otherKey : other.id = key := beq_iff_eq.mp otherMatches
      exact congrArg some (same_id snapshot rowMem (List.mem_of_find?_eq_some source)
        (rowKey.trans otherKey.symm))

private theorem lookup_amount (snapshot : Snapshot) (key : Int64) :
    snapshot.readTable.get key.toInt =
      (snapshot.rows.find? fun row => row.id == key).map fun row =>
        [.integer key, .integer row.amount] := by
  rw [snapshot.readTable.get_eq, ← find_ordered snapshot key]
  exact lookup_rows key snapshot.orderedRows

theorem execute_seek_snapshot (snapshot : Snapshot) (key : Int64) (query : Shell.Query)
    (selected : query.key = some key) :
    let projected := ((snapshot.rows.find? fun row => row.id == key).toList).map fun row =>
      query.columns.map fun column => match column with
        | .id => key.toInt
        | .amount => row.amount.toInt
    Shell.execute snapshot.readTable query =
      .ok ⟨query.columns.map Shell.Column.name, (projected.drop query.offset).take (query.limit.getD 1)⟩ := by
  cases found : snapshot.rows.find? (fun row => row.id == key) with
  | none =>
    have missing : snapshot.readTable.get key.toInt = none := by
      simpa [found] using lookup_amount snapshot key
    simpa [found] using Shell.execute_seek_query_none snapshot.readTable key query selected missing
  | some row =>
    have hit : snapshot.readTable.get key.toInt = some [.integer key, .integer row.amount] := by
      simpa [found] using lookup_amount snapshot key
    rw [Shell.execute_seek_query_some snapshot.readTable key row.amount query selected hit]
    rfl

end Silmaril.Proofs.Formats.Sqlite.Shell.Seek.Snapshot
