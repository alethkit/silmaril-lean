module

public import Silmaril.Formats.Sqlite.Shell.Defs
public import Silmaril.Formats.Sqlite.WriteProfile.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.Scan.Read

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- The ordinary two-column scan returns exactly the snapshot rows in their
signed rowid order. -/
theorem execute_scan (snapshot : WriteProfile.Snapshot) :
    execute snapshot.readTable { columns := [.id, .amount] } =
      .ok ⟨["id", "amount"], snapshot.orderedRows.map fun row => [row.id.toInt, row.amount.toInt]⟩ :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Scan.execute_scan snapshot

end Silmaril.Formats.Sqlite.Shell
