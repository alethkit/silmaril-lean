module

public import Silmaril.Formats.Sqlite.Shell.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.Seek.Read

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- The point query emits no rows when its key is absent. -/
theorem execute_seek_none (table : Vdbe.Table) (key : Int64)
    (missing : table.get key.toInt = none) :
    execute table { columns := [.id, .amount], key := some key } = .ok ⟨["id", "amount"], []⟩ :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Seek.execute_seek_none table key missing

/-- The point query emits the exact key and amount of a selected typed row. -/
theorem execute_seek_some (table : Vdbe.Table) (key amount : Int64)
    (found : table.get key.toInt = some [.integer key, .integer amount]) :
    execute table { columns := [.id, .amount], key := some key } =
      .ok ⟨["id", "amount"], [[key.toInt, amount.toInt]]⟩ :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Seek.execute_seek_some table key amount found

end Silmaril.Formats.Sqlite.Shell
