module

public import Silmaril.Formats.Sqlite.Shell.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.Parser.Parse

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- An accepted SELECT projects one of the four supported column lists.
Positive offset requires a parsed LIMIT. -/
theorem parse?_projection_and_offset {sql : String} {query : Query}
    (parsed : parse? sql = some query) :
    (query.columns = [.id, .amount] ∨ query.columns = [.amount, .id] ∨
      query.columns = [.id] ∨ query.columns = [.amount]) ∧
    (query.limit = none → query.offset = 0) :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Parser.parse?_projection_and_offset parsed

end Silmaril.Formats.Sqlite.Shell
