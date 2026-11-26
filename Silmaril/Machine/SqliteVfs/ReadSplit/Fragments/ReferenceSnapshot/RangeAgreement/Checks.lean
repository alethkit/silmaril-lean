module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement.Thms

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement

open Silmaril.Machine.SqliteVfs

private def initial : FileState := ⟨[44, 13], some .readOnly, 0⟩
private def otherSnapshot : Bytes := [90, 13]
private def token : Handle := ⟨0⟩

private theorem read_backing_contract (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

example : ReadsSnapshot (readOnly 8) otherSnapshot token initial 1 [1, 1] := by
  have original : ReadsSnapshot (readOnly 8) initial.bytes token initial 1 [1, 1] :=
    ⟨read_backing_contract initial.bytes 1 1, read_backing_contract initial.bytes 2 1, trivial⟩
  refine (readsSnapshot_iff_of_range_agreement (readOnly 8) initial.bytes otherSnapshot token
    initial 1 [1, 1] ?_ ?_).mp original
  · intro n hn
    have : n = 1 := by simpa using hn
    omega
  · intro i inside
    change i < 2 at inside
    have possible : i = 0 ∨ i = 1 := by omega
    rcases possible with rfl | rfl <;> rfl

example : readBacking ([42] : Bytes) 1 0 = .ok [] ∧
    readBacking ([] : Bytes) 1 0 = .shortRead [] := by
  decide

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement
