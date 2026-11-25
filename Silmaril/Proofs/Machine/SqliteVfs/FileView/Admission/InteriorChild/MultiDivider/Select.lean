module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
import Silmaril.Formats.Sqlite.File.Thms
import Silmaril.Machine.SqliteVfs.FileView.Admission.Thms
import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf (btreeHeaderOffset)
open Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

theorem decoded_signed_order (view : File.View) (base : Nat) (interior : Interior)
    (parsed : Interior.read? view base = some interior) :
    interior.dividers.Pairwise (fun left right => left.upperKey < right.upperKey) := by
  unfold Interior.read? at parsed
  split at parsed
  · contradiction
  · split at parsed
    · cases parsed
      assumption
    · contradiction

/-- When all earlier signed dividers are smaller and this divider includes
the key, the selected pointer is its left child. -/
theorem choose_at_divider (page : Interior) (key : Int) (earlier later : List Divider)
    (current : Divider) (split : page.dividers = earlier ++ current :: later)
    (past : ∀ divider ∈ earlier, divider.upperKey < key) (bound : key ≤ current.upperKey) :
    page.choose key = current.leftChild := by
  have found : page.dividers.find? (fun divider => decide (key ≤ divider.upperKey)) = some current :=
    List.find?_eq_some_iff_append.mpr ⟨by simpa, earlier, later, split, fun cell membership => by
      simpa using Int.not_le.mpr (past cell membership)⟩
  simp [Interior.choose, found]

/-- If every signed divider is smaller, choose the separately encoded
rightmost child. -/
theorem choose_rightmost (page : Interior) (key : Int)
    (past : ∀ divider ∈ page.dividers, divider.upperKey < key) :
    page.choose key = page.rightmost := by
  have missed : page.dividers.find? (fun divider => decide (key ≤ divider.upperKey)) = none :=
    List.find?_eq_none.mpr fun cell membership => by
      simpa using Int.not_le.mpr (past cell membership)
  simp [Interior.choose, missed]

theorem multi_child_admitted (image : File.Image) (handle : Handle) (root : Nat)
    (key : Int) (bytes : Bytes) (child : Page)
    (selected : selectMultipleChild? image handle root key bytes = some child) :
    child.handle = handle ∧ child.size = image.header.pageSize ∧ child.Admitted ∧
      ∃ view, image.page? child.number = some view := by
  unfold selectMultipleChild? at selected
  dsimp only at selected
  split at selected
  · contradiction
  · rename_i interior decoded
    split at selected
    · contradiction
    · cases found : image.page? (interior.choose key) with
      | none => simp [found] at selected
      | some view =>
        simp only [found] at selected
        split at selected
        · cases selected
          exact ⟨rfl, rfl, ‹_›, view, found⟩
        · contradiction

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
      bytes.length = view.length ∧ ∀ index, index < view.length → bytes[index]? = view.get? index := by
  obtain ⟨handleEq, sizeEq, _, view, found⟩ :=
    multi_child_admitted image handle root key rootBytes child selected
  cases child with
  | mk childHandle number size =>
    change childHandle = handle at handleEq
    change size = image.header.pageSize at sizeEq
    subst childHandle
    subst size
    obtain ⟨bytes, filled, length, agrees⟩ :=
      FileView.Admission.parsed_image_page_fill capacity first.file image number view handle
        first.cache slot parsed snapshot found live owned
    refine ⟨view, bytes, found, ?_, length, agrees⟩
    simpa [NextPage.fillFollowing, accepted, selected] using congrArg some filled

private theorem page_complete (image : File.Image) (number : Nat) (view : File.View)
    (file : FileState) (snapshot : file.bytes = image.source.toList)
    (found : image.page? number = some view) :
    (number - 1) * image.header.pageSize + image.header.pageSize ≤ file.bytes.length := by
  obtain ⟨_, _, sourceEq, startEq, lengthEq⟩ := File.Image.page?_spec image number view found
  have bounded := view.bounded
  rw [sourceEq, startEq, lengthEq] at bounded
  simpa [snapshot] using bounded

/-- With the parsed root and same live snapshot, perform the exact cold
root/child reads into their distinct owned slots. -/
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
      Trace.Valid (readOnly capacity) file (first.trace ++ next.trace) next.file := by
  let rootPage : Page := ⟨handle, root, image.header.pageSize⟩
  obtain ⟨handleEq, sizeEq, childAdmitted, childView, childFound⟩ :=
    multi_child_admitted image handle root key _ child selected
  have rootAdmitted := FileView.Admission.parsed_image_page_admitted handle parsed rootFound
  have childLive : (file.mode child.handle).isNone = false := by rw [handleEq]; exact live
  have childComplete : child.offset + child.size ≤ file.bytes.length := by
    simpa only [Page.offset, sizeEq] using page_complete image child.number childView file snapshot childFound
  exact NextPage.readOnly_selected_full_fills capacity file cache rootSlot childSlot rootPage child
    (selectMultipleChild? image handle root key) distinct rootOwned childOwned rootAdmitted childAdmitted
    live childLive (page_complete image root rootView file snapshot rootFound) childComplete selected

end Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider
