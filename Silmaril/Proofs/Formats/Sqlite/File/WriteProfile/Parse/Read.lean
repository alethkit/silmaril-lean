module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Parse

private theorem all_frame {values : List Nat} {f g : Nat → Bool}
    (same : ∀ i, i ∈ values → f i = g i) : values.all f = values.all g := by
  induction values with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.all_cons, same i (by simp), ih (fun j hj => same j (by simp [hj]))]

private theorem fold_frame {values : List Nat} {f g : Nat → Nat → Option Nat}
    (acc : Nat) (same : ∀ i, i ∈ values → ∀ n, f n i = g n i) :
    values.foldlM f acc = values.foldlM g acc := by
  induction values generalizing acc with
  | nil => rfl
  | cons i rest ih =>
    have tail (n : Nat) := ih n fun j hj => same j (by simp [hj])
    simp only [List.foldlM_cons, same i (by simp), tail]

private theorem parseHeader_frame (left right : Bytes)
    (leftFits : 100 ≤ left.length) (rightFits : 100 ≤ right.length)
    (same : ∀ i, i < 100 → (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i) :
    File.parseHeader? left = File.parseHeader? right := by
  have field (offset width : Nat) (fits : offset + width ≤ 100) :
      (File.View.ofBytes left).be? offset width = (File.View.ofBytes right).be? offset width := by
    unfold File.View.be?
    apply fold_frame
    intro i member _
    have inside := List.mem_range.mp member
    rw [same (offset + i) (by omega)]
  have magic : (List.range 16).all (fun i => (File.View.ofBytes left).get? i == File.headerMagic[i]?) =
      (List.range 16).all (fun i => (File.View.ofBytes right).get? i == File.headerMagic[i]?) := by
    apply all_frame
    intro i member
    have inside := List.mem_range.mp member
    rw [same i (by omega)]
  have reserved : (List.range 20).all (fun i => (File.View.ofBytes left).get? (72+i) == some 0) =
      (List.range 20).all (fun i => (File.View.ofBytes right).get? (72+i) == some 0) := by
    apply all_frame
    intro i member
    have inside := List.mem_range.mp member
    rw [same (72+i) (by omega)]
  unfold File.parseHeader?
  simp only [ite_eq_right (Nat.not_lt.mpr leftFits), ite_eq_right (Nat.not_lt.mpr rightFits), magic, reserved,
    field 16 2 (by decide), field 18 1 (by decide), field 19 1 (by decide), field 20 1 (by decide),
    field 21 1 (by decide), field 22 1 (by decide), field 23 1 (by decide), field 44 4 (by decide),
    field 56 4 (by decide), field 52 4 (by decide), field 64 4 (by decide), field 24 4 (by decide),
    field 28 4 (by decide), field 32 4 (by decide), field 36 4 (by decide), field 40 4 (by decide),
    field 48 4 (by decide), field 60 4 (by decide), field 68 4 (by decide), field 92 4 (by decide),
    field 96 4 (by decide)]

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
      rw [parseHeader_frame _ (Bytes.ofList File.Write.header)
        (by simp [File.Write.header_length]) (by simp [File.Write.header_length])
        (header_prefix_read _), header_template_exact]
  simp [File.parse?, reads, size, expectedHeader, File.Header.pageCountValid]

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Parse
