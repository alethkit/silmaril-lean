module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Thms

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies

open Silmaril.Machine.SqliteVfs.ReadInterval (presentCount)

private def checked (bytes : Bytes) : FileState := ⟨bytes, some .readOnly, 0⟩
private def token : Handle := ⟨0⟩
private def initial : FileState := checked [99, 7, 13]
private def changed : FileState := checked [99, 90, 13]
private def reference : Bytes := [11, 7, 13]
private def view (state : FileState × Nat) : Bytes := state.1.bytes
private def updating : Handler (FileState × Nat) := fun state request =>
  let call := readOnly 8 state.1 request
  (call.1, { call.2 with bytes := changed.bytes }, state.2 + 1)

private theorem readBacking_result (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

example :
    ReadResult reference 1 3 (.shortRead [7, 13, 0]) ∧
      (readFragments updating token (initial, 4) 1 1 [2]).file = (changed, 6) := by
  have tail : ReadsAgreeingViews updating view reference token (changed, 5) 2 [2] :=
    cons_of_matching_reply updating view reference token (changed, 5) 2 2 [] (by decide)
      (readBacking_result reference 2 2) (readBacking_result changed.bytes 2 2)
      rfl (fun _ => rfl) trivial
  have both : ReadsAgreeingViews updating view reference token (initial, 4) 1 [1, 2] :=
    cons_of_matching_reply updating view reference token (initial, 4) 1 1 [2] (by decide)
      (readBacking_result reference 1 1) (readBacking_result initial.bytes 1 1)
      rfl (fun short => False.elim ((by decide : ¬ 3 < 2) short)) tail
  have snapshot := readsSnapshot_of_agreeing_views updating view reference token (initial, 4) 1 [1, 2] both
  obtain ⟨reply, value, result⟩ :=
    (read_fragments_snapshot_contract updating reference token (initial, 4) 1 1 [2] snapshot).1
  change some (.shortRead [7, 13, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨result, rfl⟩

private def shortReference : Bytes := [11, 8]
private def withTrailingZero : FileState := checked [99, 8, 0]

-- A present zero and an absent byte produce the same padding, but not the
-- optional-byte agreement needed by the per-call contract.
example :
    let reply := (readOnly 8 withTrailingZero (.read token 1 3)).1
    reply = readBacking shortReference 1 3 ∧
      ReadResult withTrailingZero.bytes 1 3 reply ∧ ReadResult shortReference 1 3 reply ∧
      presentCount shortReference 1 3 ≠ presentCount withTrailingZero.bytes 1 3 ∧
      ¬ ReadsAgreeingViews (readOnly 8) FileState.bytes shortReference token withTrailingZero 1 [3] := by
  dsimp only
  refine ⟨rfl, readBacking_result withTrailingZero.bytes 1 3,
    readBacking_result shortReference 1 3, by decide, ?_⟩
  intro agreement
  have impossible := agreement.2.1 1 (by decide)
  change (none : Option UInt8) = some 0 at impossible
  cases impossible

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies
