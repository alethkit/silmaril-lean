module

import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf.Thms
meta import Silmaril.Formats.Sqlite.File.Defs
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Defs
meta import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs
meta import Silmaril.Machine.SqliteVfs.PageRead.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

-- Distinct header locations on the first and later pages.
private def source : Silmaril.Formats.Bytes :=
  ⟨⟨File.headerMagic.toArray ++ #[2, 0, 1, 1, 0, 64, 32, 32] ++
    Array.replicate 76 0 ++ #[5] ++ Array.replicate 411 0 ++
    #[5] ++ Array.replicate 99 0 ++ #[13] ++ Array.replicate 411 0⟩⟩

private def rejectsAfterFill (number : Nat) : Bool :=
  let base := FileView.Admission.VdbeLeaf.btreeHeaderOffset number
  let rejects (view : File.View) :=
    (FileView.VdbeLeaf.run? view base 0 2 #[.halt 0] 1 .initial).isNone
  match File.parse? source with
  | none => false
  | some image =>
    match image.page? number with
    | none => false
    | some original =>
      let page : Page := ⟨⟨0⟩, number, image.header.pageSize⟩
      let file : FileState := ⟨image.source.toList, some .readOnly, 0⟩
      let cache : Cache := fun slot => if slot = 0 then some .vacant else none
      let filled := fill (readOnly 1024) file cache 0 page
      match filled.result, filled.trace with
      | .ok data, [⟨.read handle offset count, .ok reply⟩] =>
        let copied := File.View.ofBytes (Silmaril.Formats.Bytes.ofList data)
        original.get? base == some 5 && copied.get? base == some 5 &&
          data == original.materialize.toList && reply == data &&
          handle == page.handle && offset == Int.ofNat page.offset && count == 512 &&
          filled.file == file && filled.cache 0 == some (.resident page data) &&
          rejects original && rejects copied
      | _, _ => false

#guard rejectsAfterFill 1
#guard rejectsAfterFill 2

#print axioms parsed_nonleaf_full_fill_rejects

end Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf
