module

import Silmaril.Machine.SqliteVfs.ReadInterval.Subinterval.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs

namespace Silmaril.Machine.SqliteVfs.ReadInterval.Subinterval

open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews

example {left right : Bytes} {offset size skip count : Nat}
    (within : skip + count ≤ size)
    (samePrefix : presentCount left offset size = presentCount right offset size) :
    presentCount left (offset + skip) count = presentCount right (offset + skip) count := by
  rw [presentCount_subinterval left offset size skip count within,
    presentCount_subinterval right offset size skip count within, samePrefix]

private def handle : Handle := ⟨0⟩
private def before : FileState := ⟨[], some .readOnly, 0⟩
private def after : FileState := ⟨[99, 88, 0], some .readOnly, 0⟩
private def reference : Bytes := [0]

private def growing : Handler FileState := fun state request =>
  let call := readOnly 8 state request
  (call.1, { call.2 with bytes := after.bytes })

private theorem readBacking_result (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

-- The summed present counts agree, but the actual schedule replaces an
-- already-missing first byte by introducing a later real zero.
example :
    let first := growing before (.read handle 0 2)
    let second := growing first.2 (.read handle 2 2)
    first.1 = readBacking reference 0 2 ∧ second.1 = readBacking reference 2 2 ∧
      ReadResult before.bytes 0 2 first.1 ∧ ReadResult first.2.bytes 2 2 second.1 ∧
      presentCount before.bytes 0 2 + presentCount first.2.bytes 2 2 = presentCount reference 0 4 ∧
      (readFragments growing handle before 0 2 [2]).file = after ∧
      ¬ ReadsAgreeingViews growing FileState.bytes reference handle before 0 [2, 2] := by
  dsimp only
  refine ⟨rfl, rfl, readBacking_result before.bytes 0 2, readBacking_result after.bytes 2 2,
    rfl, rfl, ?_⟩
  intro agrees
  have missing := agrees.2.1 0 (by decide)
  change (some (0 : UInt8)) = none at missing
  cases missing

end Silmaril.Machine.SqliteVfs.ReadInterval.Subinterval
