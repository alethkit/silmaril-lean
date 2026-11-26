module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
public import Silmaril.Formats.Sqlite.Shell.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Insert.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.Reopen.Thms
import Silmaril.Formats.Sqlite.Shell.CheckedImage.Thms
import Silmaril.Formats.Sqlite.WriteProfile.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.Shell.Transaction

open WriteProfile

private theorem insert_fresh {snapshot : Snapshot} {id amount : Int64} {edited : Edited}
    (inserted : snapshot.insert id amount = .ok edited) : ¬ snapshot.has id := by
  simp only [Snapshot.insert] at inserted
  split at inserted
  · assumption
  · cases inserted

private theorem open_checked {snapshot : Snapshot} {bytes : Bytes}
    (encoded : Image.Checked.encode snapshot = .ok bytes) :
    TableLeaf.open? bytes = some snapshot.readTable := by
  rw [Image.Checked.encode_eq_mapError] at encoded
  cases result : Image.encode snapshot with
  | error error => simp [result, Except.mapError] at encoded
  | ok actual =>
    have same : actual = bytes := by simpa [result, Except.mapError] using encoded
    exact Image.encode_open_table (same ▸ result)

theorem begin_insert_query (snapshot : Snapshot) (id amount : Int64) {edited : Edited}
    {original : Bytes} (inserted : snapshot.insert id amount = .ok edited)
    (encoded : Image.Checked.encode snapshot = .ok original) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    let insertedCell := (⟨id, Record.Write.amount amount⟩ : BTree.LeafWrite.Cell).bytes
    let used := 8 + 2 * snapshot.orderedRows.length + cells.flatten.length + 2 + insertedCell.length
    let query : Shell.Query := ⟨[.id, .amount], some id, none, 0, false⟩
    let begun := step ⟨snapshot, none⟩ .begin
    let pending := step begun.state (.edit (.insert (.integer id) (.integer amount)))
    let commitResult := step pending.state .commit
    let rollbackResult := step pending.state .rollback
    begun.result = .ok .transaction ∧
    pending.result = .ok (.changed 1) ∧
    commitResult.result = .ok .transaction ∧ rollbackResult.result = .ok .transaction ∧
    Image.Checked.encode rollbackResult.state.visible = .ok original ∧
    TableLeaf.open? original = some snapshot.readTable ∧
    (TableLeaf.open? original).map (fun table => Shell.execute table query) =
      some (.ok ⟨["id", "amount"], []⟩) ∧
    ((∃ bytes, Image.Checked.encode commitResult.state.visible = .ok bytes ∧
        bytes.length = 1024 ∧ TableLeaf.open? bytes = some edited.snapshot.readTable ∧
        (TableLeaf.open? bytes).map (fun table => Shell.execute table query) =
          some (.ok ⟨["id", "amount"], [[id.toInt, amount.toInt]]⟩)) ↔ used ≤ File.Write.pageSize) ∧
    (Image.Checked.encode commitResult.state.visible = .error (.encode (.tablePage .pageFull)) ↔
      File.Write.pageSize < used) := by
  have accepted : snapshot.apply (.insert (.integer id) (.integer amount)) = .ok edited := by
    change snapshot.insert id amount = .ok edited
    exact inserted
  have rows := insert_rows snapshot accepted
  have queryOrig : snapshot.rows.find? (fun row => row.id == id) = none := by
    apply List.find?_eq_none.mpr
    intro row member equal
    exact insert_fresh inserted ((beq_iff_eq.mp equal) ▸ List.mem_map_of_mem member)
  have queryAfter : edited.snapshot.rows.find? (fun row => row.id == id) = some ⟨id, amount⟩ := by
    simp [rows.1]
  dsimp only
  have begun : step (⟨snapshot, none⟩ : State) .begin =
      ⟨⟨snapshot, some snapshot⟩, .ok .transaction⟩ := rfl
  rw [begun, pending_edit _ rfl accepted, WriteProfile.commit _ rfl, WriteProfile.rollback _ rfl]
  have changed : (Except.ok (.changed edited.changed) : Except Error Success) =
      .ok (.changed 1) := by rw [rows.2]
  refine ⟨rfl, changed, rfl, rfl, encoded, open_checked encoded, ?_, ?_,
    (Image.Checked.insert_image_capacity inserted).2⟩
  · simpa [queryOrig, Shell.Column.name] using
      Shell.execute_checked_query encoded ⟨[.id, .amount], some id, none, 0, false⟩
  · have capacity := (Image.Checked.insert_image_capacity inserted).1
    constructor
    · rintro ⟨bytes, accepted, size, reopened, _⟩
      exact capacity.mp ⟨bytes, accepted, size, reopened⟩
    · intro fits
      obtain ⟨bytes, accepted, size, reopened⟩ := capacity.mpr fits
      refine ⟨bytes, accepted, size, reopened, ?_⟩
      simpa [queryAfter, Shell.Column.name] using
        Shell.execute_checked_query accepted ⟨[.id, .amount], some id, none, 0, false⟩

end Silmaril.Proofs.Formats.Sqlite.Shell.Transaction
