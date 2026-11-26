module

public import Silmaril.Machine.SqliteVfs.ReadInterval.Defs
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadInterval

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadInterval (presentCount)

/-- Matching contracted replies determine the requested optional bytes.
A matching present-prefix count is needed only for short reads. -/
theorem recover_optional_bytes {before after : Bytes} {offset count : Nat}
    {beforeReply afterReply : ReadReply} (_admitted : ReadRange offset count)
    (beforeRead : ReadResult before offset count beforeReply)
    (afterRead : ReadResult after offset count afterReply)
    (sameReply : beforeReply = afterReply)
    (shortCount : before.length < offset + count →
      presentCount before offset count = presentCount after offset count) :
    ∀ i, i < count → before[offset + i]? = after[offset + i]? := by
  obtain ⟨beforeBuffer, beforeStatus, _, beforeAt⟩ := beforeRead
  obtain ⟨afterBuffer, afterStatus, _, afterAt⟩ := afterRead
  rw [beforeStatus, afterStatus] at sameReply
  have agreement : beforeBuffer = afterBuffer ∧
      (offset + count ≤ before.length ↔ offset + count ≤ after.length) := by
    split at sameReply <;> split at sameReply <;> cases sameReply <;> simp [*]
  have counts : presentCount before offset count = presentCount after offset count := by
    by_cases full : offset + count ≤ before.length
    · have otherFull := agreement.2.mp full
      unfold presentCount
      omega
    · exact shortCount (by omega)
  intro i inside
  have cut (data : Bytes) : i < presentCount data offset count ↔ offset + i < data.length := by
    unfold presentCount
    rw [Nat.lt_min]
    omega
  have bothPresent : offset + i < before.length ↔ offset + i < after.length := by
    rw [← cut before, ← cut after, counts]
  by_cases present : offset + i < before.length
  · have otherPresent := bothPresent.mp present
    have bytes := beforeAt i inside
    rw [agreement.1, afterAt i inside] at bytes
    simpa [List.getElem?_eq_getElem present, List.getElem?_eq_getElem otherPresent] using bytes.symm
  · have otherMissing := mt bothPresent.mpr present
    rw [List.getElem?_eq_none_iff.mpr (by omega : before.length ≤ offset + i),
      List.getElem?_eq_none_iff.mpr (by omega : after.length ≤ offset + i)]

end Silmaril.Proofs.Machine.SqliteVfs.ReadInterval
