module

public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf (btreeHeaderOffset)

structure Divider where
  leftChild : Nat
  upperKey : Int
  start : Nat
  stop : Nat
  deriving Repr

structure Interior where
  dividers : List Divider
  rightmost : Nat

/-- Decode a packed 512-byte table interior page in pointer order. Use byte
extents only to check the packing, since physical cell order may differ. -/
def Interior.read? (view : File.View) (base : Nat) : Option Interior :=
  match readPacked? with
  | none => none
  | some interior =>
    if interior.dividers.Pairwise (fun left right => left.upperKey < right.upperKey) then
      some interior
    else none
where
  packed : Nat → Nat → List Divider → Bool
    | start, stop, [] => start == stop
    | start, stop, cell :: rest => cell.start == start && packed cell.stop stop rest

  readPacked? : Option Interior := do
    guard (view.length == 512 && view.get? base == some 5)
    guard (view.be? (base + 1) 2 == some 0 && view.get? (base + 7) == some 0)
    let count ← view.be? (base + 3) 2
    let content ← view.be? (base + 5) 2
    guard (count > 0 && base + 12 + 2 * count ≤ content && content ≤ view.length)
    let rightmost ← view.be? (base + 8) 4
    let dividers ← (List.range count).mapM fun index => do
      let start ← view.be? (base + 12 + 2 * index) 2
      guard (content ≤ start && start + 4 < view.length)
      let child ← view.be? start 4
      let (key, stop) ← Varint.read? view (start + 4)
      pure ⟨child, File.signed 8 key.toNat, start, stop⟩
    guard (packed content view.length (dividers.mergeSort fun a b => decide (a.start ≤ b.start)))
    pure ⟨dividers, rightmost⟩

def Interior.choose (page : Interior) (key : Int) : Nat :=
  match page.dividers.find? (fun divider => decide (key ≤ divider.upperKey)) with
  | some divider => divider.leftChild
  | none => page.rightmost

def selectMultipleChild? (image : File.Image) (handle : Handle) (root : Nat) (key : Int)
    (bytes : Bytes) : Option Page :=
  let view := File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes)
  match Interior.read? view (btreeHeaderOffset root) with
  | none => none
  | some interior =>
    let number := interior.choose key
    if image.header.pageSize != 512 || image.header.reserved != 0 ||
        number == root || number == image.header.lockPage || image.header.isPointerMapPage number then
      none
    else
      match image.page? number with
      | none => none
      | some _ =>
        let page : Page := ⟨handle, number, image.header.pageSize⟩
        if page.Admitted then some page else none

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider
