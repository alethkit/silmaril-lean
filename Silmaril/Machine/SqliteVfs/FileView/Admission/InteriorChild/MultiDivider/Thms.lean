module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
import Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Select

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf (btreeHeaderOffset)

/-- A decoded pointer array has strictly increasing signed divider keys. -/
theorem decoded_signed_order (view : File.View) (base : Nat) (interior : Interior)
    (parsed : Interior.read? view base = some interior) :
    interior.dividers.Pairwise (fun left right => left.upperKey < right.upperKey) :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.decoded_signed_order
    view base interior parsed

/-- The first divider whose inclusive interval contains the key chooses its left child. -/
theorem choose_at_divider (page : Interior) (key : Int) (earlier later : List Divider)
    (current : Divider) (split : page.dividers = earlier ++ current :: later)
    (past : ∀ divider ∈ earlier, divider.upperKey < key) (bound : key ≤ current.upperKey) :
    page.choose key = current.leftChild :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.choose_at_divider
    page key earlier later current split past bound

/-- A key greater than every divider chooses the header's rightmost child. -/
theorem choose_rightmost (page : Interior) (key : Int)
    (past : ∀ divider ∈ page.dividers, divider.upperKey < key) :
    page.choose key = page.rightmost :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.choose_rightmost
    page key past

/-- A chosen child is present and admitted on the same handle. -/
theorem multi_child_admitted (image : File.Image) (handle : Handle) (root : Nat)
    (key : Int) (bytes : Bytes) (child : Page)
    (selected : selectMultipleChild? image handle root key bytes = some child) :
    child.handle = handle ∧ child.size = image.header.pageSize ∧ child.Admitted ∧
      ∃ view, image.page? child.number = some view :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.multi_child_admitted
    image handle root key bytes child selected

/-- The accepted root buffer selects one exact child fill from the current cache and backing. -/
theorem multi_child_full_fill (capacity : Nat) (image : File.Image) (handle : Handle)
    (root : Nat) (child : Page) (key : Int) (first : Outcome FileState) (slot : SlotId)
    {source : Silmaril.Formats.Bytes} {rootBytes : Bytes}
    (parsed : File.parse? source = some image) (accepted : first.result = .ok rootBytes)
    (selected : selectMultipleChild? image handle root key rootBytes = some child)
    (snapshot : first.file.bytes = image.source.toList)
    (live : (first.file.mode handle).isNone = false) (owned : first.cache slot = some .vacant) :
    ∃ view bytes, image.page? child.number = some view ∧
      NextPage.fillFollowing (readOnly capacity) first slot
          (selectMultipleChild? image handle root key) =
        some ⟨.ok bytes, first.file, first.cache.install slot child bytes, [⟨child.request, .ok bytes⟩]⟩ ∧
      bytes.length = view.length ∧ ∀ index, index < view.length → bytes[index]? = view.get? index :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.multi_child_full_fill
    capacity image handle root child key first slot parsed accepted
    selected snapshot live owned

/-- A selected child of a parsed root yields the exact valid two-read trace and both cache installs. -/
theorem parsed_multi_child_reads (capacity : Nat) (image : File.Image) (handle : Handle)
    (root : Nat) (rootView : File.View) (child : Page) (key : Int) (file : FileState)
    (cache : Cache) (rootSlot childSlot : SlotId) {source : Silmaril.Formats.Bytes}
    (parsed : File.parse? source = some image) (rootFound : image.page? root = some rootView)
    (snapshot : file.bytes = image.source.toList) (live : (file.mode handle).isNone = false)
    (distinct : childSlot ≠ rootSlot) (rootOwned : cache rootSlot = some .vacant)
    (childOwned : cache childSlot = some .vacant)
    (selected : selectMultipleChild? image handle root key
      (readBytes file.bytes ((root - 1) * image.header.pageSize) image.header.pageSize) = some child) :
    let rootPage : Page := ⟨handle, root, image.header.pageSize⟩
    let rootBytes := readBytes file.bytes rootPage.offset rootPage.size
    let childBytes := readBytes file.bytes child.offset child.size
    let first := fill (readOnly capacity) file cache rootSlot rootPage
    let next := fill (readOnly capacity) first.file first.cache childSlot child
    NextPage.fillFollowing (readOnly capacity) first childSlot (selectMultipleChild? image handle root key) =
        some next ∧
      first.result = .ok rootBytes ∧ next.result = .ok childBytes ∧ next.file = file ∧
      next.cache = (cache.install rootSlot rootPage rootBytes).install childSlot child childBytes ∧
      first.trace ++ next.trace = [⟨rootPage.request, .ok rootBytes⟩, ⟨child.request, .ok childBytes⟩] ∧
      Trace.Valid (readOnly capacity) file (first.trace ++ next.trace) next.file :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.parsed_multi_child_reads
    capacity image handle root rootView child key file cache rootSlot
    childSlot parsed rootFound snapshot live distinct rootOwned childOwned selected

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider
