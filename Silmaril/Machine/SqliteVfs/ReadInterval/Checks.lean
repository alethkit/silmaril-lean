module

import Silmaril.Machine.SqliteVfs.ReadInterval.Thms

namespace Silmaril.Machine.SqliteVfs.ReadInterval

private theorem readBacking_result (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

example : ∀ i, i < 2 → ([99, 7, 0] : Bytes)[1 + i]? = ([22, 7, 0, 99] : Bytes)[1 + i]? :=
  recover_optional_bytes (by decide) (readBacking_result [99, 7, 0] 1 2)
    (readBacking_result [22, 7, 0, 99] 1 2) rfl (fun short => False.elim ((by decide : ¬ 3 < 3) short))

example : ∀ i, i < 3 → ([11, 8] : Bytes)[1 + i]? = ([99, 8] : Bytes)[1 + i]? :=
  recover_optional_bytes (by decide) (readBacking_result [11, 8] 1 3)
    (readBacking_result [99, 8] 1 3) rfl (fun _ => rfl)

example :
    readBacking [11, 8] 1 3 = .shortRead [8, 0, 0] ∧
      readBacking [99, 8, 0] 1 3 = .shortRead [8, 0, 0] ∧
      presentCount [11, 8] 1 3 = 1 ∧ presentCount [99, 8, 0] 1 3 = 2 ∧
      ([11, 8] : Bytes)[2]? = none ∧ ([99, 8, 0] : Bytes)[2]? = some 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Silmaril.Machine.SqliteVfs.ReadInterval
