module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.Defs
public import Silmaril.Machine.SqliteVfs.FileView.Admission.Thms
public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Thms
import Silmaril.Formats.Sqlite.File.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild (selectChild?)

theorem selected_child_admitted (image : File.Image) (handle : Handle) (root : Nat)
    (key : Int64) (bytes : Bytes) (child : Page)
    (selected : selectChild? image handle root key bytes = some child) :
    child.handle = handle ∧ child.size = image.header.pageSize ∧ child.Admitted ∧
      ∃ view, image.page? child.number = some view := by
  unfold selectChild? at selected
  split at selected
  · contradiction
  · rename_i number decoded
    split at selected
    · contradiction
    · cases found : image.page? number with
      | none => simp [found] at selected
      | some view =>
        simp only [found] at selected
        split at selected
        · cases selected
          exact ⟨rfl, rfl, ‹_›, view, found⟩
        · contradiction

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
      bytes.length = view.length ∧ ∀ i, i < view.length → bytes[i]? = view.get? i := by
  obtain ⟨handleEq, sizeEq, _, view, found⟩ :=
    selected_child_admitted image handle root key rootBytes child chosen
  cases child with
  | mk childHandle number size =>
    change childHandle = handle at handleEq
    change size = image.header.pageSize at sizeEq
    subst childHandle
    subst size
    obtain ⟨bytes, filled, length, agrees⟩ := FileView.Admission.parsed_image_page_fill
      capacity first.file image number view handle first.cache target parsed snapshot found live owned
    refine ⟨view, bytes, found, ?_, length, agrees⟩
    simpa [NextPage.fillFollowing, accepted, chosen] using congrArg some filled

private theorem page_complete (image : File.Image) (number : Nat) (view : File.View)
    (file : FileState) (snapshot : file.bytes = image.source.toList)
    (found : image.page? number = some view) :
    (number - 1) * image.header.pageSize + image.header.pageSize ≤ file.bytes.length := by
  obtain ⟨_, _, sourceEq, startEq, lengthEq⟩ := File.Image.page?_spec image number view found
  have bounded := view.bounded
  rw [sourceEq, startEq, lengthEq] at bounded
  simpa [snapshot] using bounded

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
      Trace.Valid (readOnly capacity) file (first.trace ++ next.trace) next.file := by
  let rootPage : Page := ⟨handle, root, image.header.pageSize⟩
  obtain ⟨handleEq, sizeEq, childAdmitted, childView, childFound⟩ :=
    selected_child_admitted image handle root key _ child chosen
  have rootAdmitted := FileView.Admission.parsed_image_page_admitted handle parsed rootFound
  have childLive : (file.mode child.handle).isNone = false := by rw [handleEq]; exact live
  have childComplete : child.offset + child.size ≤ file.bytes.length := by
    simpa only [Page.offset, sizeEq] using page_complete image child.number childView file snapshot childFound
  exact NextPage.readOnly_selected_full_fills capacity file cache rootSlot childSlot rootPage child
    (selectChild? image handle root key) distinct rootOwned childOwned rootAdmitted childAdmitted
    live childLive (page_complete image root rootView file snapshot rootFound) childComplete chosen

end Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild
