module

public import Silmaril.Formats.Sqlite.File.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Formats.Sqlite.File.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView

open Silmaril.Machine.SqliteVfs
open Silmaril.Formats.Sqlite.File (View Image)

private theorem readBytes_get_view (file : FileState) (view : View)
    (snapshot : file.bytes = view.source.toList) (i : Nat) (inside : i < view.length) :
    (readBytes file.bytes view.start view.length)[i]? = view.get? i := by
  have within : view.start + i < view.source.data.size := by
    have bounded := view.bounded
    change view.start + view.length ≤ view.source.data.size at bounded
    omega
  have element : view.source.toList[view.start + i]? = some view.source.data[view.start + i] :=
    calc
      _ = view.source.data.data[view.start + i]? := Array.getElem?_toList
      _ = _ := Array.getElem?_eq_getElem within
  simp only [readBytes, List.getElem?_ofFn, dite_eq_left inside, View.get?, ite_eq_left inside,
    snapshot, element, Option.getD_some]
  exact (getElem?_pos view.source.data _ within).symm

private theorem readBytes_get_page (file : FileState) (image : Image) (number : Nat) (view : View)
    (snapshot : file.bytes = image.source.toList)
    (page : image.page? number = some view) (i : Nat) (inside : i < image.header.pageSize) :
    (readBytes file.bytes ((number - 1) * image.header.pageSize) image.header.pageSize)[i]? =
      view.get? i := by
  obtain ⟨_, _, source, start, size⟩ := Image.page?_spec image number view page
  simpa only [start, size] using readBytes_get_view file view (source ▸ snapshot) i (size ▸ inside)

theorem image_page_trace (capacity : Nat) (file : FileState) (image : Image) (number : Nat)
    (view : View) (handle : Handle) (snapshot : file.bytes = image.source.toList)
    (page : image.page? number = some view) (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize) :
    let offset := (number - 1) * image.header.pageSize
    ∃ bytes, Trace.Valid (readOnly capacity) file
      [⟨.read handle offset image.header.pageSize, .ok bytes⟩] file ∧
      bytes.length = view.length ∧ ∀ i, i < view.length → bytes[i]? = view.get? i := by
  dsimp only
  obtain ⟨_, _, source, start, size⟩ := Image.page?_spec image number view page
  have fits : (number - 1) * image.header.pageSize + image.header.pageSize ≤ file.bytes.length := by
    simpa only [start, size, source, snapshot, Silmaril.Formats.Bytes.length_toList] using view.bounded
  let bytes := readBytes file.bytes ((number - 1) * image.header.pageSize) image.header.pageSize
  refine ⟨bytes, .cons ?_ (.nil _), ?_, ?_⟩
  · simp only [backing, live, Bool.false_eq_true, ↓reduceIte, range, Int.toNat_natCast, readBacking, fits, bytes]
  · simp [bytes, size, readBytes]
  · intro i inside
    exact readBytes_get_page file image number view snapshot page i (size ▸ inside)

theorem image_page_fill (capacity : Nat) (file : FileState) (image : Image) (number : Nat)
    (view : View) (handle : Handle) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    ∃ bytes, PageRead.fill (readOnly capacity) file cache target page =
      ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      bytes.length = view.length ∧ ∀ i, i < view.length → bytes[i]? = view.get? i := by
  let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
  obtain ⟨positive, _, source, start, size⟩ := Image.page?_spec image number view found
  have fits : page.offset + page.size ≤ file.bytes.length := by
    simpa only [page, PageRead.Page.offset, start, size, source, snapshot,
      Silmaril.Formats.Bytes.length_toList] using view.bounded
  let bytes := readBytes file.bytes page.offset page.size
  refine ⟨bytes, ?_, ?_, ?_⟩
  · have filled := PageRead.readOnly_fill capacity file cache target page owned ⟨positive, range⟩ live
    exact (ite_eq_left fits).mp filled
  · simp [bytes, page, size, readBytes]
  · intro i inside
    exact readBytes_get_page file image number view snapshot found i (size ▸ inside)

end Silmaril.Proofs.Machine.SqliteVfs.FileView
