module

import Silmaril.Formats.Sqlite.File.Thms
import Silmaril.Formats.Sqlite.Varint.Thms
import Silmaril.Formats.Sqlite.Record.Raw.Thms

open Silmaril.Formats Silmaril.Formats.Sqlite

private def check (message : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError message)

private def requireSome {α : Type} (message : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError message)

/-- Inspect the only local payload in the fixture's ordinary table leaf. -/
private def payload (image : File.Image) : Option (UInt64 × Nat × Bytes) := do
  let page ← image.usablePage? 2
  guard (page.be? 0 1 == some 13 && page.be? 3 2 == some 1)
  let cell ← page.be? 8 2
  let (size, keyStart) ← Varint.readNat? page cell
  let (key, bodyStart) ← Varint.read? page keyStart
  let record ← page.sub? bodyStart size
  pure (key, bodyStart - keyStart, record.materialize)

private def fixture (path : String) (encoding : File.TextEncoding)
    (encodedText : List UInt8) : IO Unit := do
  let source : Bytes := ⟨← IO.FS.readBinFile path⟩
  let image ← requireSome "native fixture header" (File.parse? source)
  check "512-byte pages in native fixture" (image.header.pageSize == 512)
  check "native text encoding" (image.header.encoding == encoding)
  let (key, width, record) ← requireSome "native table leaf payload" (payload image)
  check "native nine-byte signed64 rowid" (key == 9223372036854775807 && width == 9)
  let raw ← requireSome "native raw record" (Record.decodeRaw? record)
  match raw.toList with
  | [.integer flag, .text text, .blob blob, .null] =>
    check "raw stored types and text bytes"
      (flag == -129 && text.toList == encodedText && blob.toList == [0, 255])
  | _ => throw (IO.userError "unexpected raw storage classes")
  let projected ← requireSome "native decoded record" (Record.decode? encoding record)
  match projected.toList with
  | [.integer flag, .text text, .blob blob, .null] =>
    check "decoded text and storage classes" (flag == -129 && text == "Aé" && blob.toList == [0, 255])
  | _ => throw (IO.userError "unexpected decoded storage classes")
  check "fixture preserved" (source.data == (← IO.FS.readBinFile path))

public def main (args : List String) : IO Unit := do
  let [utf8, utf16le, utf16be] := args | throw (IO.userError "provide three fresh fixture paths")
  check "reject truncated database headers" (File.parse? (Bytes.ofList [83, 81, 76])).isNone
  check "one-byte varint"
    (Varint.read? (File.View.ofBytes (Bytes.ofList [127])) 0 == some (127, 1))
  check "reject truncated varint"
    (Varint.read? (File.View.ofBytes (Bytes.ofList [128])) 0).isNone
  check "reject truncated record"
    (Record.decodeRaw? (Bytes.ofList [2, 7, 0])).isNone
  fixture utf8 .utf8 [65, 195, 169]
  fixture utf16le .utf16le [65, 0, 233, 0]
  fixture utf16be .utf16be [0, 65, 0, 233]
  IO.println "PASS native UTF-8, UTF-16LE and UTF-16BE headers, rowids, records and file preservation"
