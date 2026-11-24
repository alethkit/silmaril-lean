module
public import Silmaril.Formats.Sqlite.Varint.Defs

/-! Persistent SQLite record headers and serial types. Text and blob payloads
remain zero-copy views, including malformed text: strict Unicode decoding is
a separate semantic projection. Reserved serial types 10 and 11 are modeled
but rejected by the persistent record reader. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.Record

inductive SerialType where
  | null | integer (width : Nat) | real | zero | one
  | reserved (code : Nat) | blob (length : Nat) | text (length : Nat)
  deriving DecidableEq, Repr

def serialType (code : Nat) : SerialType :=
  match code with
  | 0 => .null | 1 => .integer 1 | 2 => .integer 2 | 3 => .integer 3
  | 4 => .integer 4 | 5 => .integer 6 | 6 => .integer 8 | 7 => .real
  | 8 => .zero | 9 => .one | 10 => .reserved 10 | 11 => .reserved 11
  | n => if n % 2 == 0 then .blob ((n-12)/2) else .text ((n-13)/2)

def SerialType.width : SerialType → Nat
  | .null | .zero | .one | .reserved _ => 0
  | .integer width => width | .real => 8
  | .blob length | .text length => length

structure Column where
  code : Nat
  payload : File.View

structure Parsed where
  source : File.View
  headerSize : Nat
  columns : Array Column

def headerAux? (source : File.View) (stop : Nat) : Nat → Nat → Option (List Nat)
  | 0, offset => if offset == stop then some [] else none
  | fuel+1, offset =>
    if offset == stop then some [] else if offset > stop then none else do
      let (code,next) ← Varint.readNat? source offset
      if next > stop then none else pure (code :: (← headerAux? source stop fuel next))

def columnsAux? (source : File.View) : List Nat → Nat → Option (List Column × Nat)
  | [], offset => some ([],offset)
  | code :: codes, offset =>
    match serialType code with
    | .reserved _ => none
    | kind => do
      let width := kind.width
      let payload ← source.sub? offset width
      let (rest,next) ← columnsAux? source codes (offset+width)
      pure (⟨code,payload⟩ :: rest,next)

def parse? (source : File.View) : Option Parsed := do
  let (headerSize,first) ← Varint.readNat? source 0
  if headerSize < first || headerSize > source.length then none else do
    let codes ← headerAux? source headerSize headerSize first
    let (columns,next) ← columnsAux? source codes headerSize
    if next != source.length then none else some ⟨source,headerSize,columns.toArray⟩

def unicodeUnits? (encoding : File.TextEncoding) (source : File.View) : Option (List Nat) :=
  if !(encoding == .utf16le || encoding == .utf16be) || source.length % 2 != 0 then none else
    (List.range (source.length/2)).mapM fun i =>
      if encoding == .utf16le then source.le? (2*i) 2 else source.be? (2*i) 2

def decodeUnits? : List Nat → Option (List Char)
  | [] => some []
  | high :: rest =>
    if high < 0xd800 || high > 0xdfff then
      (Char.ofNat high :: ·) <$> decodeUnits? rest
    else if high > 0xdbff then none else
      match rest with
      | [] => none
      | low :: tail =>
        if low < 0xdc00 || low > 0xdfff then none else
          (Char.ofNat (0x10000+(high-0xd800)*1024+(low-0xdc00)) :: ·) <$> decodeUnits? tail

def decodeText? (encoding : File.TextEncoding) (source : File.View) : Option String :=
  match encoding with
  | .unspecified => none
  | .utf8 => String.fromUTF8? source.materialize.data
  | .utf16le | .utf16be => String.ofList <$> ((unicodeUnits? encoding source).bind decodeUnits?)

def Column.value? (encoding : File.TextEncoding) (column : Column) : Option Value :=
  match serialType column.code with
  | .null => some .null
  | .zero => some (.integer 0)
  | .one => some (.integer 1)
  | .integer width => do
    let n ← column.payload.be? 0 width
    pure (.integer (Int64.ofInt (File.signed width n)))
  | .real => do
    pure (.real (UInt64.ofNat (← column.payload.be? 0 8)))
  | .blob _ => some (.blob column.payload.materialize)
  | .text _ => Value.text <$> decodeText? encoding column.payload
  | .reserved _ => none

def Parsed.values? (encoding : File.TextEncoding) (record : Parsed) : Option (Array Value) :=
  (record.columns.toList.mapM (Column.value? encoding)).map List.toArray

def decode? (encoding : File.TextEncoding) (bytes : Bytes) : Option (Array Value) :=
  (parse? (File.View.ofBytes bytes)).bind (Parsed.values? encoding)
end Silmaril.Formats.Sqlite.Record
