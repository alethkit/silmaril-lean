module

public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Proofs.Formats.Sqlite.Record.Write.Amount

public section
namespace Silmaril.Formats.Sqlite.Record.Write

/-- The fixed-width record keeps the rowid-alias NULL slot and the exact signed
64-bit amount. Text encoding does not affect either storage class. -/
theorem decode_amount (encoding : File.TextEncoding) (value : Int64) :
    Record.decode? encoding (Bytes.ofList (amount value)) =
      some #[.null, .integer value] :=
  Silmaril.Proofs.Formats.Sqlite.Record.Write.decode_amount encoding value

end Silmaril.Formats.Sqlite.Record.Write
