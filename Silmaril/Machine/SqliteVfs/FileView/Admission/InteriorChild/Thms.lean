module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
import Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.Select

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- A successful selection checks the chosen page lookup and its VFS bounds. -/
theorem selected_child_admitted (image : File.Image) (handle : Handle) (root : Nat)
    (key : Int64) (bytes : Bytes) (child : Page)
    (selected : selectChild? image handle root key bytes = some child) :
    child.handle = handle ∧ child.size = image.header.pageSize ∧ child.Admitted ∧
      ∃ view, image.page? child.number = some view :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.selected_child_admitted
    image handle root key bytes child selected

/-- A choice from an accepted root buffer fills a present child exactly,
using the actual backing and slot state returned by the first operation. -/
theorem selected_child_full_fill (capacity : Nat) (image : File.Image) (handle : Handle)
    (root : Nat) (child : Page) (key : Int64) (first : Outcome FileState) (target : SlotId)
    {source : Silmaril.Formats.Bytes} {rootBytes : Bytes}
    (parsed : File.parse? source = some image) (accepted : first.result = .ok rootBytes)
    (chosen : selectChild? image handle root key rootBytes = some child)
    (snapshot : first.file.bytes = image.source.toList)
    (live : (first.file.mode handle).isNone = false) (owned : first.cache target = some .vacant) :
    ∃ view bytes, image.page? child.number = some view ∧
      NextPage.fillFollowing (readOnly capacity) first target (selectChild? image handle root key) =
        some ⟨.ok bytes, first.file, first.cache.install target child bytes,
          [⟨child.request, .ok bytes⟩]⟩ ∧
      bytes.length = view.length ∧ ∀ i, i < view.length → bytes[i]? = view.get? i :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.selected_child_full_fill
    capacity image handle root child key first target parsed accepted chosen snapshot live owned

/-- For this chosen child of a parsed-image root read, two owned slots
receive the exact two page buffers with two ordered successful exchanges. -/
theorem parsed_root_child_reads (capacity : Nat) (image : File.Image) (handle : Handle)
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
    NextPage.fillFollowing (readOnly capacity) first childSlot (selectChild? image handle root key) = some next ∧
      first.result = .ok rootBytes ∧ next.result = .ok childBytes ∧ next.file = file ∧
      next.cache = (cache.install rootSlot rootPage rootBytes).install childSlot child childBytes ∧
      first.trace ++ next.trace = [⟨rootPage.request, .ok rootBytes⟩, ⟨child.request, .ok childBytes⟩] ∧
      Trace.Valid (readOnly capacity) file (first.trace ++ next.trace) next.file :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.parsed_root_child_reads
    capacity image handle root rootView child key file cache rootSlot childSlot
    parsed rootFound snapshot live distinct rootOwned childOwned chosen

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild
