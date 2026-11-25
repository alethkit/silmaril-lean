module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend.Thms
public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Thms
import Silmaril.Machine.SqliteVfs.FileView.Admission.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.FileView.Admission (parsed_image_page_fill)
open Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend (parsed_image_page_fill_query query)
open Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild
open Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf (btreeHeaderOffset)

/-- Compare the restricted query on the selected copy and on the original
image view. Both receive the same page-relative header offset. -/
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
            (btreeHeaderOffset child.number) sql = query view (btreeHeaderOffset child.number) sql := by
  dsimp only
  obtain ⟨followed, _, nextBytes, nextFile, nextCache, exactTrace, valid⟩ :=
    parsed_root_child_reads capacity image handle root rootView child key file cache rootSlot childSlot
      parsed rootFound snapshot live distinct rootOwned childOwned chosen
  obtain ⟨sameHandle, sameSize, _, view, found⟩ :=
    selected_child_admitted image handle root key _ child chosen
  let first := fill (readOnly capacity) file cache rootSlot ⟨handle, root, image.header.pageSize⟩
  obtain ⟨_, rootFill, _, _⟩ :=
    parsed_image_page_fill capacity file image root rootView handle cache rootSlot
      parsed snapshot rootFound live rootOwned
  have firstFile : first.file = file := congrArg Outcome.file rootFill
  have firstOwned : first.cache childSlot = some .vacant :=
    (fill_other (readOnly capacity) file cache rootSlot _ childSlot distinct).trans childOwned
  obtain ⟨_, queriedBytes, queryFill, equalQuery⟩ :=
    parsed_image_page_fill_query capacity first.file image child.number view handle first.cache
      childSlot parsed (firstFile ▸ snapshot) found (firstFile ▸ live) firstOwned
  have childPage : (⟨handle, child.number, image.header.pageSize⟩ : Page) = child := by
    cases child
    simp_all
  rw [childPage] at queryFill
  have sameBytes : queriedBytes = readBytes file.bytes child.offset child.size :=
    Except.ok.inj ((congrArg Outcome.result queryFill).symm.trans nextBytes)
  let next := fill (readOnly capacity) first.file first.cache childSlot child
  have warm := Acquire.acquire_hit (readOnly capacity) next.file next.cache childSlot child (bytes :=
    readBytes file.bytes child.offset child.size) (by
      dsimp only [next, first]
      rw [nextCache]
      simp [CacheHit.lookup, Cache.install])
  exact ⟨followed, nextFile, nextCache, exactTrace, valid, warm, view, found, sameBytes ▸ equalQuery⟩

end Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.Frontend
