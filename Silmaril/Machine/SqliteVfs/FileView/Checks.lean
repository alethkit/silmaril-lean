module

import Silmaril.Machine.SqliteVfs.FileView.Thms

namespace Silmaril.Machine.SqliteVfs.FileView

open Silmaril.Formats.Sqlite.File (Header Image View)

-- A small page geometry exercises the read offset without a database fixture.
private def header : Header := {
  pageSize := 2, writeVersion := 1, readVersion := 1, reserved := 0
  changeCounter := 1, rawPageCount := 2, freelistTrunk := 0, freelistCount := 0
  schemaCookie := 0, schemaFormat := 0, cacheSize := 0, largestRoot := 0
  encoding := .unspecified, userVersion := 0, incrementalVacuum := false
  applicationId := 0, versionValidFor := 1, sqliteVersion := 0
}

private def source : Silmaril.Formats.Bytes := .ofList [10, 20, 30, 40, 50]
private def image : Image := ⟨source, header, 2, 2⟩
private def view : View := ⟨source, 2, 2, by decide⟩
private def handle : Handle := ⟨0⟩
private def file : FileState := ⟨[10, 20, 30, 40, 50], some .readOnly, 0⟩
private def page : PageRead.Page := ⟨handle, 2, 2⟩
private def cache : PageRead.Cache
  | 0 => some .vacant
  | 1 => some (.resident ⟨handle, 1, 2⟩ [10, 20])
  | _ => none

example : ∃ bytes, Trace.Valid (readOnly 8) file
    [⟨.read handle 2 2, .ok bytes⟩] file ∧ bytes.length = 2 ∧
    ∀ i, i < 2 → bytes[i]? = view.get? i :=
  image_page_trace 8 file image 2 view handle rfl rfl rfl (by decide)

example : ∃ bytes,
    let outcome := PageRead.fill (readOnly 8) file cache 0 page
    outcome.result = .ok bytes ∧
      outcome.cache 0 = some (.resident page bytes) ∧ outcome.cache 1 = cache 1 ∧
      bytes[0]? = some 30 ∧ bytes[1]? = some 40 := by
  obtain ⟨bytes, filled, _, pointwise⟩ :=
    image_page_fill 8 file image 2 view handle cache 0 rfl rfl rfl (by decide) rfl
  change PageRead.fill (readOnly 8) file cache 0 page = _ at filled
  refine ⟨bytes, ?_, ?_, ?_, pointwise 0 (by decide), pointwise 1 (by decide)⟩ <;> rw [filled] <;> rfl

example : (image.page? 3).isNone = true := rfl

#print axioms image_page_trace
#print axioms image_page_fill

end Silmaril.Machine.SqliteVfs.FileView
