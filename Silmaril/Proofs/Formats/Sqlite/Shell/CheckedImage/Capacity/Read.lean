module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Spec.Thms
public import Silmaril.Formats.Sqlite.Shell.CheckedImage.Thms

public section

open Silmaril.Formats
open Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.Shell.CheckedImage.Capacity

theorem execute_checked_queries_iff_fits (snapshot : WriteProfile.Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    (∃ bytes : Bytes, WriteProfile.Image.Checked.encode snapshot = .ok bytes ∧ bytes.length = 1024 ∧
      ∀ query : Shell.Query, ∃ result : Shell.Result,
        (TableLeaf.open? bytes).map (fun table => Shell.execute table query) = some (.ok result)) ↔
      8 + 2 * snapshot.orderedRows.length + cells.flatten.length ≤ File.Write.pageSize := by
  dsimp only
  constructor
  · rintro ⟨bytes, encoded, _, _⟩
    apply Nat.le_of_not_gt
    intro overflow
    have full := (WriteProfile.Image.Checked.encode_pageFull_iff snapshot).mpr overflow
    rw [encoded] at full
    cases full
  · intro fits
    obtain ⟨bytes, encoded, size, _⟩ := (WriteProfile.Image.Checked.open_iff_fits snapshot).mpr fits
    refine ⟨bytes, encoded, size, ?_⟩
    intro query
    exact ⟨_, Shell.execute_checked_query encoded query⟩

end Silmaril.Proofs.Formats.Sqlite.Shell.CheckedImage.Capacity
