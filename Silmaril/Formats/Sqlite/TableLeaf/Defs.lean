module

public import Silmaril.Formats.Sqlite.Record.Defs
public import Silmaril.Formats.Sqlite.IntTable.Defs
public import Silmaril.Formats.Sqlite.BTree.Query.ReadModel.Defs

@[expose] public section
namespace Silmaril.Formats.Sqlite.TableLeaf

structure Cell where
  key : Int64
  payload : Bytes
  start : Nat
  stop : Nat

def cell? (page : File.View) (start : Nat) : Option Cell := do
  let (length, keyAt) ← Varint.readNat? page start
  guard (length ≤ 477)
  let (key, payloadAt) ← Varint.read? page keyAt
  let payload ← page.sub? payloadAt length
  let stop := max (payloadAt + length) (start + 4)
  guard (stop ≤ page.length)
  pure ⟨Int64.ofInt (File.signed 8 key.toNat), payload.materialize, start, stop⟩

def packed : Nat → Nat → List Cell → Bool
  | next, stop, [] => next == stop
  | next, stop, cell :: tail => cell.start == next && packed cell.stop stop tail

/-- Parse a packed table leaf without freeblocks, fragments or overflow. The
pointer array sets key order. Physical cell extents may occur in any order. -/
def read? (page : File.View) (base : Nat) : Option (List Cell) := do
  guard (page.length == 512 && page.get? base == some 13)
  guard (page.be? (base + 1) 2 == some 0 && page.get? (base + 7) == some 0)
  let count ← page.be? (base + 3) 2
  let content ← page.be? (base + 5) 2
  guard (base + 8 + 2 * count ≤ content && content ≤ 512)
  let cells ← (List.range count).mapM fun slot => do
    let offset ← page.be? (base + 8 + 2 * slot) 2
    guard (content ≤ offset && offset < 512)
    cell? page offset
  guard (packed content 512 (cells.mergeSort fun a b => decide (a.start ≤ b.start)))
  guard (decide (cells.Pairwise fun a b => a.key.toInt < b.key.toInt))
  pure cells

def row? (cell : Cell) : Option (Int × List Value) := do
  let fields ← Record.decode? .utf8 cell.payload
  match fields.toList with
  | [.null, .integer amount] => some (cell.key.toInt, [.integer cell.key, .integer amount])
  | _ => none

/-- The single-table file profile. This accepts a two-page, UTF-8 database
with the exact catalogue and record schema stated above. -/
def open? (source : Bytes) : Option (BTree.Query.ReadModel Int (List Value)) := do
  let image ← File.parse? source
  let header := image.header
  guard (image.pageCount == 2 && image.physicalPageCount == 2 && header.pageSize == 512)
  guard (header.encoding == .utf8 && header.reserved == 0 && header.schemaFormat == 4)
  guard (header.readVersion == 1 && header.writeVersion == 1 && !header.autoVacuum)
  guard (header.freelistTrunk == 0 && header.freelistCount == 0)
  let [schema] ← read? (← image.page? 1) 100 | none
  guard (schema.key == 1)
  guard (Record.decode? .utf8 schema.payload ==
    some #[.text "table", .text "sample", .text "sample", .integer 2, .text IntTable.schemaSql])
  let rows ← (← read? (← image.page? 2) 0).mapM row?
  pure (BTree.Query.ReadModel.ofList rows)

end Silmaril.Formats.Sqlite.TableLeaf
