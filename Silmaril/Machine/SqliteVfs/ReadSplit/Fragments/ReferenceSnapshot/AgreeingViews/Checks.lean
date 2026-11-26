module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews

open Silmaril.Machine.SqliteVfs

private def token : Handle := ⟨0⟩
private def initial : FileState := ⟨[7, 13], some .readOnly, 0⟩
private def changed : FileState := { initial with bytes := [9, 13] }
private def updating : Handler (FileState × Nat) := fun state request =>
  let call := readOnly 8 state.1 request
  (call.1, { call.2 with bytes := changed.bytes }, state.2 + 1)

private theorem readBacking_result (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

private theorem agrees_at_one : ∀ i, i < 1 → initial.bytes[1 + i]? = changed.bytes[1 + i]? := by
  intro i inside
  have zero : i = 0 := by omega
  subst i
  rfl

private theorem absent_at_two : ∀ i, i < 1 → initial.bytes[2 + i]? = changed.bytes[2 + i]? := by
  intro i inside
  have zero : i = 0 := by omega
  subst i
  rfl

example :
    ReadResult initial.bytes 0 3 (.shortRead [7, 13, 0]) ∧
      (readFragments updating token (initial, 4) 0 1 [1, 1]).file = (changed, 7) := by
  have reads : ReadsAgreeingViews updating (fun state => state.1.bytes) initial.bytes token (initial, 4) 0 [1, 1, 1] :=
    ⟨by decide, fun _ _ => rfl, readBacking_result initial.bytes 0 1,
      by decide, agrees_at_one, readBacking_result changed.bytes 1 1,
      by decide, absent_at_two, readBacking_result changed.bytes 2 1, trivial⟩
  have reference := readsSnapshot_of_agreeing_views updating _ initial.bytes token (initial, 4) 0 [1, 1, 1] reads
  obtain ⟨reply, value, result⟩ :=
    (read_fragments_snapshot_contract updating initial.bytes token (initial, 4) 0 1 [1, 1] reference).1
  change some (.shortRead [7, 13, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨result, rfl⟩

private def short : FileState := { initial with bytes := [7] }
private def grown : FileState := { initial with bytes := [9, 0] }
private def growing : Handler FileState := fun state request =>
  let call := readOnly 8 state request
  (call.1, { call.2 with bytes := grown.bytes })

example :
    (growing grown (.read token 1 1)).1 = .ok [0] ∧
    readBacking short.bytes 1 1 = .shortRead [0] ∧
    ¬ ReadsSnapshot growing short.bytes token short 0 [1, 1] := by
  refine ⟨rfl, rfl, ?_⟩
  intro reads
  obtain ⟨buffer, status, _⟩ := reads.2.1
  change ReadReply.ok [0] = .shortRead buffer at status
  cases status

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews
