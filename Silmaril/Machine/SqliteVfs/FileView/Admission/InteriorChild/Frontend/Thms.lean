module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend.Defs
public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
import Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend.Query

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open _root_.Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend (query)
open _root_.Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf (btreeHeaderOffset)

/-- The selected child is installed by an exact two-read trace. Reacquiring the
resident child makes no VFS request, and its copied bytes give the same
restricted frontend result as the original selected view. -/
theorem parsed_root_child_query (capacity : Nat) (image : File.Image) (handle : Handle)
    (root : Nat) (rootView : File.View) (child : Page) (key : Int64) (file : FileState)
    (cache : Cache) (rootSlot childSlot : SlotId) {source : Silmaril.Formats.Bytes}
    (parsed : File.parse? source = some image) (rootFound : image.page? root = some rootView)
    (snapshot : file.bytes = image.source.toList) (live : (file.mode handle).isNone = false)
    (distinct : childSlot ≠ rootSlot) (rootOwned : cache rootSlot = some .vacant)
    (childOwned : cache childSlot = some .vacant)
    (chosen : selectChild? image handle root key
      (readBytes file.bytes ((root - 1) * image.header.pageSize) image.header.pageSize) = some child) :
    let rootPage : Page := ⟨handle, root, image.header.pageSize⟩
    let rootBytes := readBytes file.bytes rootPage.offset rootPage.size
    let childBytes := readBytes file.bytes child.offset child.size
    let first := fill (readOnly capacity) file cache rootSlot rootPage
    let next := fill (readOnly capacity) first.file first.cache childSlot child
    NextPage.fillFollowing (readOnly capacity) first childSlot (selectChild? image handle root key) =
        some next ∧
      next.file = file ∧
      next.cache = (cache.install rootSlot rootPage rootBytes).install childSlot child childBytes ∧
      first.trace ++ next.trace = [⟨rootPage.request, .ok rootBytes⟩, ⟨child.request, .ok childBytes⟩] ∧
      Trace.Valid (readOnly capacity) file (first.trace ++ next.trace) next.file ∧
      Acquire.acquire (readOnly capacity) next.file next.cache childSlot child =
        ⟨.ok childBytes, next.file, next.cache, []⟩ ∧
      ∃ view, image.page? child.number = some view ∧
        ∀ sql, query (File.View.ofBytes (Silmaril.Formats.Bytes.ofList childBytes))
            (btreeHeaderOffset child.number) sql = query view (btreeHeaderOffset child.number) sql :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend.parsed_root_child_query
    capacity image handle root rootView child key file cache rootSlot childSlot
    parsed rootFound snapshot live distinct rootOwned childOwned chosen

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend
