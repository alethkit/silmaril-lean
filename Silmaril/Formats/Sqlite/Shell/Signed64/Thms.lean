module

public import Silmaril.Formats.Sqlite.Shell.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.Signed64.Parse

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- A successful signed-64 shell parse preserves the exact parsed integer. -/
theorem signed64_some_iff (text : String) (result : Int64) :
    signed64? text = some result ↔ text.toInt? = some result.toInt :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Signed64.signed64_some_iff text result

/-- The shell parser rejects tokens rejected by the integer parser and
integers outside the representable signed-64 range. -/
theorem signed64_none_iff (text : String) :
    signed64? text = none ↔ text.toInt? = none ∨
      ∃ value, text.toInt? = some value ∧ (value < -(2^63 : Int) ∨ 2^63 ≤ value) :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Signed64.signed64_none_iff text

end Silmaril.Formats.Sqlite.Shell
