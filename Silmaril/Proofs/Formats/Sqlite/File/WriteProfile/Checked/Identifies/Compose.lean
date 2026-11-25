module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Reopen.Thms
public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Canonical.Thms

public section

open Silmaril.Formats
open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Identifies

private theorem open_checked {snapshot : Snapshot} {bytes : Bytes}
    (encoded : WriteProfile.Image.Checked.encode snapshot = .ok bytes) :
    TableLeaf.open? bytes = some snapshot.readTable := by
  rw [WriteProfile.Image.Checked.encode_eq_mapError] at encoded
  have raw : WriteProfile.Image.encode snapshot = .ok bytes := by
    cases h : WriteProfile.Image.encode snapshot <;> simp_all [Except.mapError]
  exact WriteProfile.Image.encode_open_table raw

private theorem entry_injective (a b : Row) (same : a.entry = b.entry) : a = b := by
  cases a
  cases b
  simpa [Row.entry] using congrArg Prod.snd same

private theorem perm_of_common_bytes {left right : Snapshot} {bytes : Bytes}
    (first : WriteProfile.Image.Checked.encode left = .ok bytes)
    (second : WriteProfile.Image.Checked.encode right = .ok bytes) :
    left.rows.Perm right.rows := by
  have table : left.readTable = right.readTable :=
    Option.some.inj ((open_checked first).symm.trans (open_checked second))
  have entries : left.orderedRows.map Row.entry = right.orderedRows.map Row.entry :=
    congrArg BTree.Query.ReadModel.entries table
  have ordered := (List.map_inj_right entry_injective).mp entries
  have leftPerm : left.orderedRows.Perm left.rows := List.mergeSort_perm _ _
  have rightPerm : right.orderedRows.Perm right.rows := List.mergeSort_perm _ _
  rw [ordered] at leftPerm
  exact leftPerm.symm.trans rightPerm

theorem encode_eq_ok_iff_perm {left right : Snapshot} {bytes : Bytes}
    (encoded : WriteProfile.Image.Checked.encode left = .ok bytes) :
    WriteProfile.Image.Checked.encode right = .ok bytes ↔ left.rows.Perm right.rows :=
  ⟨perm_of_common_bytes encoded,
    fun rows => (WriteProfile.Image.Checked.encode_perm rows).symm.trans encoded⟩

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Identifies
