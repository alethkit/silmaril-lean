module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot

open Silmaril.Machine.SqliteVfs

private def token : Handle := ⟨0⟩
private def initial : FileState := ⟨[1, 10, 20, 30], some .readOnly, 0⟩

-- The first read changes a prefix and the second changes an already consumed byte.
private def step : Handler FileState := fun state req =>
  match req with
  | .read handle offset count =>
    let (reply, after) := readOnly 8 state (.read handle offset count)
    let bytes :=
      if offset = 1 then [90, 10, 20, 30]
      else if offset = 2 then [90, 99, 20, 30]
      else after.bytes
    (reply, { after with bytes })
  | other => readOnly 8 state other

private theorem one_byte (bytes : Bytes) (offset : Nat) :
    ReadResult bytes offset 1 (readBacking bytes offset 1) := by
  refine ⟨readBytes bytes offset 1, rfl, by simp [readBytes], ?_⟩
  intro i inside
  have indexAtZero : i = 0 := by omega
  simp [readBytes, indexAtZero]

private theorem contract : ReadsSnapshot step initial.bytes token initial 1 [1, 1, 1] :=
  ⟨one_byte initial.bytes 1, one_byte initial.bytes 2, one_byte initial.bytes 3, trivial⟩

example :
    let result := readFragments step token initial 1 1 [1, 1]
    result.reply = some (.ok [10, 20, 30]) ∧ result.file.bytes = [90, 99, 20, 30] ∧
      Trace.Valid step initial result.trace result.file :=
  ⟨rfl, rfl, (read_fragments_snapshot_contract step initial.bytes token initial 1 1 [1, 1] contract).2.1⟩

private def shortInitial : FileState := ⟨[1, 10], some .readOnly, 0⟩

private theorem short_contract :
    ReadsSnapshot (readOnly 8) shortInitial.bytes token shortInitial 1 [1, 1, 1] :=
  ⟨one_byte shortInitial.bytes 1, one_byte shortInitial.bytes 2,
    one_byte shortInitial.bytes 3, trivial⟩

example :
    let result := readFragments (readOnly 8) token shortInitial 1 1 [1, 1]
    result.reply = some (.shortRead [10, 0, 0]) ∧
      Trace.Valid (readOnly 8) shortInitial result.trace result.file :=
  ⟨rfl, (read_fragments_snapshot_contract (readOnly 8) shortInitial.bytes token
    shortInitial 1 1 [1, 1] short_contract).2.1⟩

example : ¬ ReadsSnapshot (readOnly 8) shortInitial.bytes token shortInitial 1 [1, 0, 1] := by
  intro schedule
  obtain ⟨buffer, status, _⟩ := schedule.2.1
  change ReadReply.error .invalidRange = (if 2 + 0 ≤ 2 then .ok buffer else .shortRead buffer) at status
  simp at status

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot
