module

public import Silmaril.Formats.Sqlite.Record.Raw.Defs
import Silmaril.Formats.Sqlite.Record.Raw.Thms
import Silmaril.Formats.Sqlite.File.View.Materialize.Thms
import Init.Data.ByteArray.Lemmas

public section

namespace Silmaril.Proofs.Formats.Sqlite.Record.Raw.Projection

open Silmaril.Formats Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.Record

private theorem materialize_whole (bytes : Bytes) :
    (File.View.ofBytes bytes).materialize = bytes := by
  cases bytes with
  | mk data =>
    simp [File.View.ofBytes, File.View.materialize, Bytes.length, ByteArray.extract_zero_size]

private theorem copy_get? (view : File.View) (index : Nat) :
    (File.View.ofBytes view.materialize).get? index = view.get? index := by
  by_cases inside : index < view.length
  · rw [← File.View.materialize_get? view index inside]
    simp only [File.View.get?, File.View.ofBytes, File.View.materialize_length,
      inside, ite_true, Nat.zero_add, Bytes.toList, Array.getElem?_toList]
    rfl
  · simp [File.View.get?, File.View.ofBytes, File.View.materialize_length, inside]

private theorem unicode_copy (encoding : File.TextEncoding) (view : File.View) :
    unicodeUnits? encoding (File.View.ofBytes view.materialize) = unicodeUnits? encoding view := by
  have length : (File.View.ofBytes view.materialize).length = view.length :=
    File.View.materialize_length view
  simp only [unicodeUnits?, length, File.View.be?, File.View.le?, copy_get?]

theorem decodeText?_materialize (encoding : File.TextEncoding) (view : File.View) :
    decodeText? encoding (File.View.ofBytes view.materialize) = decodeText? encoding view := by
  cases encoding <;> simp [decodeText?, materialize_whole, unicode_copy]

theorem column_raw_projection (column : Column) (encoding : File.TextEncoding) :
    column.rawValue?.bind (RawValue.toValue? encoding) = column.value? encoding := by
  cases kind : serialType column.code
  case integer width => exact Column.raw_integer_projection column width encoding kind
  case real => exact Column.raw_real_projection column encoding kind
  all_goals
    simp [Column.rawValue?, Column.value?, kind, RawValue.toValue?, decodeText?_materialize]

private theorem project_columns (encoding : File.TextEncoding) (columns : List Column) :
    (columns.mapM Column.rawValue?).bind (fun values => values.mapM (RawValue.toValue? encoding)) =
      columns.mapM (Column.value? encoding) := by
  induction columns with
  | nil => rfl
  | cons column rest ih =>
    simp only [List.mapM_cons, ← column_raw_projection column encoding, ← ih]
    cases column.rawValue? <;> cases rest.mapM Column.rawValue? <;>
      simp [bind, pure, List.mapM_cons]

theorem decodeRaw?_projection (encoding : File.TextEncoding) (bytes : Bytes) :
    (decodeRaw? bytes).bind (fun values =>
      (values.toList.mapM (RawValue.toValue? encoding)).map List.toArray) =
      decode? encoding bytes := by
  cases parsed : parse? (File.View.ofBytes bytes) with
  | none => simp [decodeRaw?, decode?, parsed]
  | some record =>
    simp only [decodeRaw?, decode?, parsed, Option.bind_some, Parsed.rawValues?, Parsed.values?]
    rw [← project_columns encoding record.columns.toList]
    cases record.columns.toList.mapM Column.rawValue? <;> simp

end Silmaril.Proofs.Formats.Sqlite.Record.Raw.Projection
