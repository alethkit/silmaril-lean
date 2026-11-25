module

import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend.Thms
meta import Silmaril.Formats.Sqlite.File.Defs
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend.Defs
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Defs
meta import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Defs
meta import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open _root_.Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend (QueryError query)

private def leaf (rowid amount serialType : UInt8) : Array UInt8 :=
  #[13, 0, 0, 0, 1, 1, 250, 0, 1, 250] ++ Array.replicate 496 0 ++
    #[4, rowid, 3, serialType, 1, amount]

private def source (leftType : UInt8) : Silmaril.Formats.Bytes :=
  ⟨⟨File.headerMagic.toArray ++ #[2, 0, 1, 1, 0, 64, 32, 32] ++ Array.replicate 488 0 ++
    #[5, 0, 0, 0, 1, 1, 251, 0, 0, 0, 0, 4, 1, 251] ++ Array.replicate 493 0 ++
    #[0, 0, 0, 3, 7] ++ leaf 7 5 leftType ++ leaf 8 6 0⟩⟩

private def exactRead (page : Page) (bytes : Bytes) : Trace → Bool
  | [⟨.read handle offset count, .ok actual⟩] =>
    handle == page.handle && offset == Int.ofNat page.offset && count == Int.ofNat page.size &&
      actual == bytes
  | _ => false

private def queryMatches (left right : Except QueryError Shell.Result) (readable : Bool)
    (rows : List (List Int)) : Bool :=
  match left, right with
  | .ok left, .ok right =>
    readable && left.columns == ["id", "amount"] && left.columns == right.columns &&
      left.rows == rows && left.rows == right.rows
  | .error .unreadableLeaf, .error .unreadableLeaf => !readable
  | _, _ => false

private def check (key : Int64) (childNumber : Nat) (leftType : UInt8)
    (readable : Bool) (rows : List (List Int)) : Bool := Id.run do
  let bytes := source leftType
  let some image := File.parse? bytes | return false
  let file : FileState := ⟨bytes.toList, some .readOnly, 1⟩
  let cache : Cache := fun slot => if slot < 2 then some .vacant else none
  let root : Page := ⟨⟨file.generation⟩, 2, image.header.pageSize⟩
  let handler := readOnly bytes.length
  let first := fill handler file cache 0 root
  let .ok rootBytes := first.result | return false
  let select := selectChild? image root.handle root.number key
  let some child := select rootBytes | return false
  let some next := NextPage.fillFollowing handler first 1 select | return false
  let .ok childBytes := next.result | return false
  let warm := Acquire.acquire handler next.file next.cache 1 child
  let .ok resident := warm.result | return false
  let some view := image.page? childNumber | return false
  let copy := File.View.ofBytes (Silmaril.Formats.Bytes.ofList resident)
  let sql := s!"select id,amount from sample where id={key.toInt}"
  let unsupported := match query copy 0 "drop table sample", query view 0 "drop table sample" with
    | .error .unsupportedSql, .error .unsupportedSql => true
    | _, _ => false
  return child.number == childNumber && exactRead root rootBytes first.trace &&
    exactRead child childBytes next.trace && next.file == file && warm.file == next.file &&
    warm.trace.isEmpty && warm.cache 0 == some (.resident root rootBytes) &&
    warm.cache 1 == some (.resident child childBytes) && warm.cache 2 == none &&
    resident == childBytes && unsupported &&
    queryMatches (query copy 0 sql) (query view 0 sql) readable rows

#guard check 7 3 0 true [[7, 5]]
#guard check 8 4 0 true [[8, 6]]
#guard check 0 3 0 true []
#guard check 7 3 8 false []

#print axioms parsed_root_child_query

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend
