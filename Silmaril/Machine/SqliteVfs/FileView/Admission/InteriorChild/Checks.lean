module

import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Thms
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Defs
meta import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
meta import Silmaril.Formats.Sqlite.File.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def packedInterior (base : Nat) (divider : Array UInt8) : Array UInt8 :=
  let content := 512 - (4 + divider.size)
  let high := UInt8.ofNat (content / 256)
  let low := UInt8.ofNat content
  #[5, 0, 0, 0, 1, high, low, 0, 0, 0, 0, 4, high, low] ++
    Array.replicate (content - (base + 14)) 0 ++ #[0, 0, 0, 3] ++ divider

private def source (divider : Array UInt8) : Silmaril.Formats.Bytes :=
  ⟨⟨File.headerMagic.toArray ++ #[2, 0, 1, 1, 0, 64, 32, 32] ++ Array.replicate 76 0 ++
    packedInterior 100 divider ++ packedInterior 0 divider ++
    Array.replicate 512 21 ++ Array.replicate 512 22⟩⟩

private def exactRead (page : Page) (bytes : Bytes) : Trace → Bool
  | [⟨.read handle offset count, .ok reply⟩] =>
    handle == page.handle && offset == Int.ofNat page.offset &&
      count == Int.ofNat page.size && reply == bytes
  | _ => false

private def checkPair (divider : Array UInt8) (root : Nat) (key : Int64) (expected : Nat) : Bool := Id.run do
  let bytes := source divider
  let some image := File.parse? bytes | return false
  let some rootView := image.page? root | return false
  let handle : Handle := ⟨0⟩
  let rootPage : Page := ⟨handle, root, image.header.pageSize⟩
  let file : FileState := ⟨bytes.toList, some .readOnly, 0⟩
  let cache : Cache := fun slot => if slot < 2 then some .vacant else none
  let handler := readOnly bytes.length
  let first := fill handler file cache 0 rootPage
  let .ok rootBytes := first.result | return false
  let select := selectChild? image handle root key
  let some child := select rootBytes | return false
  let some next := NextPage.fillFollowing handler first 1 select | return false
  let .ok childBytes := next.result | return false
  let some childView := image.page? expected | return false
  return decide rootPage.Admitted && decide child.Admitted && child.number == expected &&
    rootBytes == rootView.materialize.toList && childBytes == childView.materialize.toList &&
    first.file == file && next.file == file && next.cache 0 == some (.resident rootPage rootBytes) &&
    next.cache 1 == some (.resident child childBytes) && next.cache 2 == none &&
    exactRead rootPage rootBytes first.trace && exactRead child childBytes next.trace

private def rejectsUnsupported : Bool := Id.run do
  let some image := File.parse? (source #[63]) | return false
  let some root := image.page? 2 | return false
  let bytes := root.materialize.toList
  let select := selectChild? image ⟨0⟩ 2
  return (select 63 (bytes.set 0 13)).isNone && (select 63 (bytes.set 4 2)).isNone &&
    (select 63 (bytes.take 511)).isNone && (select 64 (bytes.set 11 0)).isNone &&
    (select 64 (bytes.set 11 2)).isNone && (select 64 (bytes.set 11 255)).isNone

#guard checkPair #[63] 1 63 3
#guard checkPair #[63] 2 64 4
#guard checkPair (Array.replicate 9 255) 2 (-1) 3
#guard checkPair (Array.replicate 9 255) 2 0 4
#guard rejectsUnsupported

#print axioms selected_child_admitted
#print axioms selected_child_full_fill
#print axioms parsed_root_child_reads

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild
