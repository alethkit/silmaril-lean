module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.Record.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Materialize.Thms
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.Thms
import Silmaril.Formats.Sqlite.TableLeaf.Subview.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Catalogue

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def source : Bytes := Bytes.ofList Record.Write.schema
private theorem source_length : source.length = 100 := rfl
private def field (code offset width : Nat) (fits : offset + width ≤ 100) : Record.Column :=
  ⟨code, ⟨source, offset, width, by rwa [source_length]⟩⟩
private def fields : Array Record.Column := #[field 23 7 5 (by decide), field 25 12 6 (by decide),
  field 25 18 6 (by decide), field 1 24 1 (by decide), field 163 25 75 (by decide)]

private theorem parse_schema : Record.parse? (File.View.ofBytes source) =
    some ⟨File.View.ofBytes source, 7, fields⟩ := rfl

private theorem fromUTF8_toByteArray (text : String) : String.fromUTF8? text.toByteArray = some text := by
  unfold String.fromUTF8?
  rw [dite_eq_left text.isValidUTF8]
  cases text
  rfl

private theorem kind_bytes : (field 23 7 5 (by decide)).payload.materialize.data = "table".toUTF8 := rfl
private theorem name_bytes : (field 25 12 6 (by decide)).payload.materialize.data = "sample".toUTF8 := rfl
private theorem table_bytes : (field 25 18 6 (by decide)).payload.materialize.data = "sample".toUTF8 := rfl
private theorem sql_bytes : (field 163 25 75 (by decide)).payload.materialize.data = IntTable.schemaSql.toUTF8 := rfl

private theorem text_value (column : Record.Column) (text : String) (length : Nat)
    (serial : Record.serialType column.code = .text length)
    (bytes : column.payload.materialize.data = text.toUTF8) :
    column.value? .utf8 = some (.text text) := by
  simp [Record.Column.value?, serial, Record.decodeText?, bytes, fromUTF8_toByteArray]

private theorem kind_value : (field 23 7 5 (by decide)).value? .utf8 = some (.text "table") :=
  text_value _ _ 5 rfl kind_bytes

private theorem name_value : (field 25 12 6 (by decide)).value? .utf8 = some (.text "sample") :=
  text_value _ _ 6 rfl name_bytes

private theorem table_value : (field 25 18 6 (by decide)).value? .utf8 = some (.text "sample") :=
  text_value _ _ 6 rfl table_bytes

private theorem root_value : (field 1 24 1 (by decide)).value? .utf8 = some (.integer 2) := rfl

private theorem sql_value : (field 163 25 75 (by decide)).value? .utf8 = some (.text IntTable.schemaSql) :=
  text_value _ _ 75 rfl sql_bytes

/-- The fixed writer catalogue record decodes to the exact strict-table schema. -/
private theorem decode_schema : Record.decode? .utf8 (Bytes.ofList Record.Write.schema) =
    some #[.text "table", .text "sample", .text "sample", .integer 2, .text IntTable.schemaSql] := by
  change (Record.parse? (File.View.ofBytes source)).bind (Record.Parsed.values? .utf8) = _
  rw [parse_schema]
  simp [Record.Parsed.values?, fields, kind_value, name_value, table_value, root_value, sql_value]

private def cell : BTree.LeafWrite.Cell := ⟨1, Record.Write.schema⟩

private theorem schema_length : Record.Write.schema.length = 100 := rfl

private theorem writer_cell : cell.bytes = [100, 1] ++ Record.Write.schema := by
  have lenCode : (Varint.encode (100 : UInt64)).toList = [100] := rfl
  have keyCode : (Varint.encode (1 : Int64).toUInt64).toList = [1] := rfl
  simp [cell, BTree.LeafWrite.Cell.bytes, schema_length, lenCode, keyCode]

private theorem read_schema_cell_prefix (tail : List UInt8) (size : tail.length = 100) :
    TableLeaf.cell? (File.View.ofBytes (Bytes.ofList ([100, 1] ++ tail))) 0 =
      some ⟨1, Bytes.ofList tail, 0, 102⟩ := by
  let source := Bytes.ofList ([100, 1] ++ tail)
  let view := File.View.ofBytes source
  have length : source.length = 102 := by simp [source, size]
  let payload : File.View := ⟨source, 2, 100, by rw [length]⟩
  have early (i : Nat) (inside : i < 2) : view.get? i = some (([100, 1] : List UInt8)[i]'inside) := by
    have within : i < source.length := by rw [length]; omega
    simp only [view, File.View.get?, File.View.ofBytes, within, ite_true, Nat.zero_add]
    have dataBound : i < ([100, 1] ++ tail).toByteArray.size := within
    rw [getElem?_pos source.data i dataBound]
    apply congrArg some
    change ([100, 1] ++ tail).toByteArray[i]'dataBound = ([100, 1] : List UInt8)[i]'inside
    rw [List.getElem_toByteArray, List.getElem_append_left inside]
  have readSize : Varint.readNat? view 0 = some (100, 1) := by
    simp only [Varint.readNat?, Varint.readAux?, early 0 (by decide), Option.bind_eq_bind, Option.bind_some]
    rfl
  have readKey : Varint.read? view 1 = some (1, 2) := by
    simp only [Varint.read?, Varint.readNat?, Varint.readAux?, early 1 (by decide), Option.bind_eq_bind,
      Option.bind_some]
    rfl
  have part : view.sub? 2 100 = some payload := by simp [view, File.View.ofBytes, File.View.sub?, length, payload]
  have material : payload.materialize = Bytes.ofList tail := by
    apply congrArg Bytes.mk
    change ([100, 1] ++ tail).toByteArray.extract 2 102 = tail.toByteArray
    rw [List.toByteArray_append]
    exact ByteArray.extract_append_eq_right (by rfl) (by simp [size])
  change TableLeaf.cell? view 0 = _
  have viewSize : view.length = 102 := length
  simp [TableLeaf.cell?, readSize, readKey, part, material, viewSize, guard]
  rfl

private theorem schemaCell_read : TableLeaf.cell? (File.View.ofBytes (Bytes.ofList cell.bytes)) 0 =
    some ⟨1, Bytes.ofList Record.Write.schema, 0, 102⟩ := by
  rw [writer_cell]
  exact read_schema_cell_prefix _ schema_length

/-- The ordinary packed table-leaf reader recovers the one emitted catalogue
cell, including the rowid, record bytes and page-local extent. -/
private theorem cataloguePage_read {page : List UInt8} (accepted : cataloguePage = .ok page) :
    TableLeaf.read? (File.View.ofBytes (Bytes.ofList page)) 100 =
      some [⟨1, Bytes.ofList Record.Write.schema, 410, 512⟩] := by
  let view := File.View.ofBytes (Bytes.ofList page)
  have layout : BTree.LeafWrite.layout File.Write.header [cell.bytes] = .ok page := by
    unfold cataloguePage BTree.LeafWrite.encode at accepted
    split at accepted
    · exact accepted
    · cases accepted
  have pageLength : view.length = 512 := by simpa [view, File.View.ofBytes] using leaf_length accepted
  have fixed := BTree.LeafWrite.layout_fixed_header layout
  change view.get? 100 = some 13 ∧ view.be? 101 2 = some 0 ∧ view.get? 107 = some 0 ∧ _ at fixed
  have counts := BTree.LeafWrite.layout_header_fields layout
  change view.be? 103 2 = some 1 ∧ view.be? 105 2 = some 410 at counts
  obtain ⟨pointer, part, sub, _, _, _, same⟩ := BTree.LeafWrite.layout_pointer_materialize 0 layout rfl
  change view.be? 108 2 = some 410 at pointer
  change view.sub? 410 102 = some part at sub
  have cellRead : TableLeaf.cell? (File.View.ofBytes part.materialize) 0 =
      some ⟨1, Bytes.ofList Record.Write.schema, 0, 102⟩ := by
    rw [same]
    exact schemaCell_read
  have onPage := TableLeaf.cell?_materialized_shift view part 410 102 0 sub _ cellRead
  change TableLeaf.cell? view 410 = some ⟨1, Bytes.ofList Record.Write.schema, 410, 512⟩ at onPage
  change TableLeaf.read? view 100 = _
  simp [TableLeaf.read?, pageLength, fixed.1, fixed.2.1, fixed.2.2.1, counts.1, counts.2,
    List.range_one, pointer, onPage, TableLeaf.packed, guard]

/-- A successful catalogue page emits exactly one schema cell. The ordinary
cell and record readers recover its physical extent and all five typed fields. -/
theorem cataloguePage_read_schema {page : List UInt8} (accepted : cataloguePage = .ok page) :
    TableLeaf.read? (File.View.ofBytes (Bytes.ofList page)) 100 =
      some [⟨1, Bytes.ofList Record.Write.schema, 410, 512⟩] ∧
    Record.decode? .utf8 (Bytes.ofList Record.Write.schema) =
      some #[.text "table", .text "sample", .text "sample", .integer 2, .text IntTable.schemaSql] :=
  ⟨cataloguePage_read accepted, decode_schema⟩

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Catalogue
