module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
public import Silmaril.Formats.Sqlite.Shell.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.CheckedImage.Capacity.Read

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- A single checked 1024-byte image can be opened and execute every typed
query exactly when the table leaf's serialized contents fit. -/
theorem execute_checked_queries_iff_fits (snapshot : WriteProfile.Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    (∃ bytes : Bytes, WriteProfile.Image.Checked.encode snapshot = .ok bytes ∧ bytes.length = 1024 ∧
      ∀ query : Query, ∃ result : Result,
        (TableLeaf.open? bytes).map (fun table => execute table query) = some (.ok result)) ↔
      8 + 2 * snapshot.orderedRows.length + cells.flatten.length ≤ File.Write.pageSize :=
  Silmaril.Proofs.Formats.Sqlite.Shell.CheckedImage.Capacity.execute_checked_queries_iff_fits snapshot

end Silmaril.Formats.Sqlite.Shell
