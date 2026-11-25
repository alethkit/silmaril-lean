module

import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Thms
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Defs
meta import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
meta import Silmaril.Formats.Sqlite.File.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def be16 (n : Nat) : Array UInt8 := #[UInt8.ofNat (n / 256), UInt8.ofNat n]

private def source (firstKey : Array UInt8) : Silmaril.Formats.Bytes :=
  let firstCell := #[0, 0, 0, 3] ++ firstKey
  let secondCell := #[0, 0, 0, 4, 9]
  let firstStart := 512 - firstCell.size
  let content := firstStart - secondCell.size
  let header := #[5, 0, 0, 0, 2] ++ be16 content ++ #[0, 0, 0, 0, 5]
  let pointers := be16 firstStart ++ be16 content
  let root := header ++ pointers ++ Array.replicate (content - 16) 0 ++ secondCell ++ firstCell
  ⟨⟨File.headerMagic.toArray ++ #[2, 0, 1, 1, 0, 64, 32, 32] ++ Array.replicate 488 0 ++
    root ++ Array.replicate 512 31 ++ Array.replicate 512 42 ++ Array.replicate 512 53⟩⟩

private def exactRead (page : Page) (bytes : Bytes) : Trace → Bool
  | [⟨.read handle offset count, .ok actual⟩] =>
    handle == page.handle && offset == Int.ofNat page.offset && count == Int.ofNat page.size &&
      actual == bytes
  | _ => false

private def check (firstKey : Array UInt8) (key : Int) (expected : Nat) : Bool := Id.run do
  let raw := source firstKey
  let some image := File.parse? raw | return false
  let file : FileState := ⟨raw.toList, some .readOnly, 0⟩
  let cache : Cache := fun slot => if slot < 2 then some .vacant else none
  let root : Page := ⟨⟨file.generation⟩, 2, image.header.pageSize⟩
  let handler := readOnly raw.length
  let first := fill handler file cache 0 root
  let .ok rootBytes := first.result | return false
  let some rootView := image.page? 2 | return false
  let select := selectMultipleChild? image root.handle 2 key
  let some child := select rootBytes | return false
  let some next := NextPage.fillFollowing handler first 1 select | return false
  let .ok childBytes := next.result | return false
  let some childView := image.page? expected | return false
  return child.number == expected && exactRead root rootBytes first.trace &&
    exactRead child childBytes next.trace && next.file == file &&
    next.cache 0 == some (.resident root rootBytes) &&
    next.cache 1 == some (.resident child childBytes) && next.cache 2 == none &&
    rootBytes == rootView.materialize.toList && childBytes == childView.materialize.toList

private def malformed : Bool := Id.run do
  let some image := File.parse? (source #[7]) | return false
  let some root := image.page? 2 | return false
  let bytes := root.materialize.toList
  let select := selectMultipleChild? image ⟨0⟩ 2
  let duplicate := bytes.set 15 251
  let swapped := (bytes.set 13 246).set 15 251
  return (select 7 duplicate).isNone && (select 7 swapped).isNone &&
    (select 7 (bytes.take 511)).isNone && (select 10 (bytes.set 11 0)).isNone

#guard check #[7] 7 3
#guard check #[7] 8 4
#guard check #[7] 9 4
#guard check #[7] 10 5
#guard check (Array.replicate 9 255) (-1) 3
#guard check (Array.replicate 9 255) 0 4
#guard malformed

#print axioms decoded_signed_order
#print axioms choose_at_divider
#print axioms choose_rightmost
#print axioms multi_child_admitted
#print axioms multi_child_full_fill
#print axioms parsed_multi_child_reads

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider
