module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Defs
import Silmaril.Machine.SqliteVfs.PageRead.ReadFrame.Thms
import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadPresence

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

theorem read_result_agreement_iff {before after : FileState} (page : Page)
    {beforeReply afterReply : ReadReply} (positive : 0 < page.size)
    (beforeRead : ReadResult before.bytes page.offset page.size beforeReply)
    (afterRead : ReadResult after.bytes page.offset page.size afterReply) :
    CacheHit.AgreesOnPage before after page ↔
      beforeReply = afterReply ∧ WriteExtent.presentCount before page = WriteExtent.presentCount after page := by
  refine ⟨fun agrees => ⟨ReadFrame.read_result_agrees page positive agrees beforeRead afterRead,
    WriteExtent.presentCount_eq_of_agreement page agrees⟩, ?_⟩
  rintro ⟨replies, counts⟩ i inside
  obtain ⟨beforeBuffer, beforeStatus, _, beforeAt⟩ := beforeRead
  obtain ⟨afterBuffer, afterStatus, _, afterAt⟩ := afterRead
  have buffers : beforeBuffer = afterBuffer := by
    rw [beforeStatus, afterStatus] at replies
    split at replies <;> split at replies <;> cases replies <;> rfl
  have present : page.offset + i < before.bytes.length ↔
      page.offset + i < after.bytes.length := by
    have cut (file : FileState) :
        i < WriteExtent.presentCount file page ↔ page.offset + i < file.bytes.length := by
      unfold WriteExtent.presentCount
      rw [Nat.lt_min]
      omega
    rw [← cut before, ← cut after, counts]
  by_cases beforePresent : page.offset + i < before.bytes.length
  · have afterPresent := present.mp beforePresent
    have obs := beforeAt i inside
    rw [buffers, afterAt i inside] at obs
    simpa [List.getElem?_eq_getElem beforePresent, List.getElem?_eq_getElem afterPresent] using obs.symm
  · have afterMissing := mt present.mpr beforePresent
    rw [List.getElem?_eq_none_iff.mpr (by omega : before.bytes.length ≤ page.offset + i),
      List.getElem?_eq_none_iff.mpr (by omega : after.bytes.length ≤ page.offset + i)]

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadPresence
