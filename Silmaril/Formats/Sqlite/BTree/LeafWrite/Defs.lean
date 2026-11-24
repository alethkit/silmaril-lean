module

public import Silmaril.Formats.Sqlite.File.Write.Defs
public import Silmaril.Formats.Sqlite.Varint.Defs

/-! A single packed 512-byte table leaf. Cell pointers preserve input key
order. This layout contains no freeblocks, fragments, or overflow pages. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite

structure Cell where
  key : Int64
  payload : List UInt8

def Cell.bytes (cell : Cell) : List UInt8 :=
  let data := (Varint.encode (UInt64.ofNat cell.payload.length)).toList ++
    (Varint.encode cell.key.toUInt64).toList ++ cell.payload
  data ++ List.replicate (4 - data.length) 0

inductive Error where
  | overflowPayload
  | pageFull
  deriving DecidableEq, Repr

def offsets : Nat → List (List UInt8) → List Nat
  | _, [] => []
  | start, cell :: cells => start :: offsets (start + cell.length) cells

/-- Place the serialized cells contiguously at the end of a page. The leading
is the database header on page 1 and empty on an ordinary leaf. -/
def layout (leading : List UInt8) (cells : List (List UInt8)) : Except Error (List UInt8) :=
  let contents := cells.flatten
  let start := File.Write.pageSize - contents.length
  let used := leading.length + 8 + 2 * cells.length
  if used + contents.length ≤ File.Write.pageSize then
    .ok (leading ++ [13, 0, 0] ++ File.Write.be 2 cells.length ++ File.Write.be 2 start ++ [0] ++
      (offsets start cells).flatMap (File.Write.be 2) ++ List.replicate (start - used) 0 ++ contents)
  else
    .error .pageFull

/-- A table leaf at this page size stores at most usableSize - 35 payload
bytes locally in a cell. Larger payloads require an overflow chain. -/
def encode (leading : List UInt8) (cells : List Cell) : Except Error (List UInt8) :=
  if cells.all (fun cell => cell.payload.length ≤ File.Write.pageSize - 35) then
    layout leading (cells.map Cell.bytes)
  else
    .error .overflowPayload

end Silmaril.Formats.Sqlite.BTree.LeafWrite
