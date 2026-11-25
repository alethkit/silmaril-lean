module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Parse.Read
import Silmaril.Formats.Sqlite.File.WriteProfile.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Parse

/-- Both ordinary page lookups in a successfully encoded raw image recover
exact views of the catalogue and table page bytes emitted by the writer. -/
theorem encode_pages {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) :
    ∃ image, File.parse? bytes = some image ∧
      ∃ catalogue table, cataloguePage = .ok catalogue ∧ tablePage snapshot = .ok table ∧
        ∃ first second,
          image.page? 1 = some first ∧ first.source = bytes ∧ first.start = 0 ∧
          first.length = 512 ∧ first.materialize = Bytes.ofList catalogue ∧
          image.page? 2 = some second ∧ second.source = bytes ∧ second.start = 512 ∧
          second.length = 512 ∧ second.materialize = Bytes.ofList table := by
  have parsed := encode_parse_image accepted
  unfold encode at accepted
  split at accepted
  next => cases accepted
  next => cases accepted
  next catalogue table catalogueOk tableOk =>
    cases accepted
    have catalogueSize : catalogue.length = 512 := leaf_length catalogueOk
    have tableSize : table.length = 512 := leaf_length tableOk
    let source := Bytes.ofList (catalogue ++ table)
    have complete : source.length = 1024 := by simp [source, catalogueSize, tableSize]
    let first : File.View := ⟨source, 0, 512, by omega⟩
    let second : File.View := ⟨source, 512, 512, by omega⟩
    refine ⟨_, parsed, catalogue, table, catalogueOk, tableOk, first, second,
      ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, ?_⟩
    · simp [File.Image.page?, File.View.sub?, File.View.ofBytes, source,
        catalogueSize, tableSize, first]
    · apply congrArg Bytes.mk
      change (catalogue ++ table).toByteArray.extract 0 512 = catalogue.toByteArray
      rw [List.toByteArray_append]
      exact ByteArray.extract_append_eq_left (by simp [catalogueSize])
    · simp [File.Image.page?, File.View.sub?, File.View.ofBytes, source,
        catalogueSize, tableSize, second]
    · apply congrArg Bytes.mk
      change (catalogue ++ table).toByteArray.extract 512 (512 + 512) = table.toByteArray
      rw [List.toByteArray_append]
      apply ByteArray.extract_append_eq_right
      · simp [catalogueSize]
      · simp [catalogueSize, tableSize]

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Parse
