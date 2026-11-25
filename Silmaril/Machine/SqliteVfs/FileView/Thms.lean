module

public import Silmaril.Formats.Sqlite.File.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.FileView.Agreement

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView

open Silmaril.Formats.Sqlite.File (Image View)

/-- An admitted read of an existing image page in the same snapshot produces
one successful VFS exchange with the unchanged file state and exactly the
physical page view's bytes. -/
theorem image_page_trace (capacity : Nat) (file : FileState) (image : Image) (number : Nat)
    (view : View) (handle : Handle) (snapshot : file.bytes = image.source.toList)
    (page : image.page? number = some view) (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize) :
    let offset := (number - 1) * image.header.pageSize
    ∃ bytes, Trace.Valid (readOnly capacity) file
      [⟨.read handle offset image.header.pageSize, .ok bytes⟩] file ∧
      bytes.length = view.length ∧ ∀ i, i < view.length → bytes[i]? = view.get? i :=
  Proofs.Machine.SqliteVfs.FileView.image_page_trace capacity file image number view handle
    snapshot page live range

/-- Under the same read premises and ownership of a vacant slot, the owned
page-fill operation installs precisely the view's bytes and frames the other
slots via `Cache.install`. -/
theorem image_page_fill (capacity : Nat) (file : FileState) (image : Image) (number : Nat)
    (view : View) (handle : Handle) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    ∃ bytes, PageRead.fill (readOnly capacity) file cache target page =
      ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      bytes.length = view.length ∧ ∀ i, i < view.length → bytes[i]? = view.get? i :=
  Proofs.Machine.SqliteVfs.FileView.image_page_fill capacity file image number view handle cache target
    snapshot found live range owned

end Silmaril.Machine.SqliteVfs.FileView
