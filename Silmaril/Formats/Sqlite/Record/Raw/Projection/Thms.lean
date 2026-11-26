module

public import Silmaril.Formats.Sqlite.Record.Raw.Defs
import Silmaril.Proofs.Formats.Sqlite.Record.Raw.Projection.Read

public section
namespace Silmaril.Formats.Sqlite.Record

/-- Copying a bounded text view preserves the exact decoding result under the
same encoding, including strict Unicode rejection. -/
theorem decodeText?_materialize (encoding : File.TextEncoding) (view : File.View) :
    decodeText? encoding (File.View.ofBytes view.materialize) = decodeText? encoding view :=
  Silmaril.Proofs.Formats.Sqlite.Record.Raw.Projection.decodeText?_materialize encoding view

/-- Raw decoding followed by semantic projection agrees with the ordinary
column decoder for every storage class. -/
theorem Column.raw_projection (column : Column) (encoding : File.TextEncoding) :
    column.rawValue?.bind (RawValue.toValue? encoding) = column.value? encoding :=
  Silmaril.Proofs.Formats.Sqlite.Record.Raw.Projection.column_raw_projection column encoding

/-- Projecting all columns of a raw record yields the exact ordinary semantic
result, including rejection. -/
theorem decodeRaw?_projection (encoding : File.TextEncoding) (bytes : Bytes) :
    (decodeRaw? bytes).bind (fun values =>
      (values.toList.mapM (RawValue.toValue? encoding)).map List.toArray) =
      decode? encoding bytes :=
  Silmaril.Proofs.Formats.Sqlite.Record.Raw.Projection.decodeRaw?_projection encoding bytes

end Silmaril.Formats.Sqlite.Record
