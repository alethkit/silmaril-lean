module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Thms
import Silmaril.Formats.Sqlite.File.Header.Frame.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Parse

private theorem header_prefix_read (tail : List UInt8) (i : Nat) (inside : i < 100) :
    (File.View.ofBytes (Bytes.ofList (File.Write.header ++ tail))).get? i =
      (File.View.ofBytes (Bytes.ofList File.Write.header)).get? i := by
  have short : i < (Bytes.ofList File.Write.header).length := by
    simpa [File.Write.header_length] using inside
  have full : i < (Bytes.ofList (File.Write.header ++ tail)).length := by
    simp [File.Write.header_length]
    omega
  simp only [File.View.get?, File.View.ofBytes, full, short, ite_true, Nat.zero_add]
  have left : i < (Bytes.ofList (File.Write.header ++ tail)).data.size := full
  have right : i < (Bytes.ofList File.Write.header).data.size := short
  rw [getElem?_pos (Bytes.ofList (File.Write.header ++ tail)).data i left,
    getElem?_pos (Bytes.ofList File.Write.header).data i right]
  apply congrArg some
  change (File.Write.header ++ tail).toByteArray[i]'left = File.Write.header.toByteArray[i]'right
  calc
    _ = (File.Write.header ++ tail)[i]'(by simpa using full) := List.getElem_toByteArray
    _ = File.Write.header[i]'(by simpa using short) := List.getElem_append_left (by simpa using short)
    _ = _ := List.getElem_toByteArray.symm

private theorem catalogue_prefix {page : List UInt8} (accepted : cataloguePage = .ok page) :
    ∃ tail, page = File.Write.header ++ tail := by
  unfold cataloguePage BTree.LeafWrite.encode at accepted
  split at accepted
  · simp only [BTree.LeafWrite.layout] at accepted
    split at accepted
    · cases accepted
      simp only [List.append_assoc]
      exact ⟨_, rfl⟩
    · cases accepted
  · cases accepted

private def expectedHeader : File.Header :=
  { pageSize := 512, writeVersion := 1, readVersion := 1, reserved := 0,
    changeCounter := 1, rawPageCount := 2, freelistTrunk := 0, freelistCount := 0,
    schemaCookie := 1, schemaFormat := 4, cacheSize := 0, largestRoot := 0,
    encoding := .utf8, userVersion := 0, incrementalVacuum := false, applicationId := 0,
    versionValidFor := 1, sqliteVersion := 0 }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem header_template_exact :
    File.parseHeader? (Bytes.ofList File.Write.header) = some expectedHeader := rfl

/-- Successful raw output has the exact expected file header and two pages
in the ordinary file parser, independently of the optional table reopen. -/
theorem encode_parse_image {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) :
    File.parse? bytes = some ⟨bytes,
      { pageSize := 512, writeVersion := 1, readVersion := 1, reserved := 0,
        changeCounter := 1, rawPageCount := 2, freelistTrunk := 0, freelistCount := 0,
        schemaCookie := 1, schemaFormat := 4, cacheSize := 0, largestRoot := 0,
        encoding := .utf8, userVersion := 0, incrementalVacuum := false, applicationId := 0,
        versionValidFor := 1, sqliteVersion := 0 }, 2, 2⟩ := by
  change File.parse? bytes = some ⟨bytes, expectedHeader, 2, 2⟩
  have size := encode_length accepted
  have reads : File.parseHeader? bytes = some expectedHeader := by
    unfold encode at accepted
    split at accepted
    next => cases accepted
    next => cases accepted
    next catalogue rows catalogueOk _ =>
      obtain ⟨tail, headerPrefix⟩ := catalogue_prefix catalogueOk
      cases accepted
      rw [headerPrefix, List.append_assoc]
      rw [File.parseHeader?_frame _ (Bytes.ofList File.Write.header)
        (by simp [File.Write.header_length]) (by simp [File.Write.header_length])
        (header_prefix_read _), header_template_exact]
  simp [File.parse?, reads, size, expectedHeader, File.Header.pageCountValid]

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Parse
