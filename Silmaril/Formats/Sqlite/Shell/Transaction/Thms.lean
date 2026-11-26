module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
public import Silmaril.Formats.Sqlite.Shell.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.Transaction.Branch

public section
namespace Silmaril.Formats.Sqlite.Shell

open WriteProfile

/-- For an accepted typed insertion into an encodable snapshot, logical
rollback restores the original image and the inserted rowid misses. If the
edited table fits, logical commit admits a fresh image with an exact point hit.
Above capacity, checked encoding of the committed snapshot returns pageFull. -/
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
      File.Write.pageSize < used) :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Transaction.begin_insert_query
    snapshot id amount inserted encoded

end Silmaril.Formats.Sqlite.Shell
