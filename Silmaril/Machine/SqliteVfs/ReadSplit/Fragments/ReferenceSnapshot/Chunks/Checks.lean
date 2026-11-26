module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks.Thms

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)

private def token : Handle := ⟨0⟩
private def file : FileState := ⟨[9, 13], some .readOnly, 0⟩
private def counted : Handler (FileState × Nat) := fun state request =>
  let call := readOnly 8 state.1 request
  (call.1, call.2, state.2 + 1)

private theorem read_backing_contract (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

example :
    ReadsSnapshot counted file.bytes token (file, 5) 1 [1, 1, 1] ∧
      (readFragments counted token (file, 5) 1 1 [1]).file = (file, 7) := by
  refine ⟨(readsSnapshot_append_iff counted file.bytes token (file, 5) 1 1 [1] [1]).mpr ?_, rfl⟩
  exact ⟨⟨read_backing_contract file.bytes 1 1, read_backing_contract file.bytes 2 1, trivial⟩,
    read_backing_contract file.bytes 3 1, trivial⟩

example :
    ¬ ReadsSnapshot counted file.bytes token (file, 5) 1 [1, 0, 1] ∧
      (readFragments counted token (file, 5) 1 1 [0, 1]).file = (file, 8) := by
  refine ⟨?_, rfl⟩
  intro contract
  have suffix := ((readsSnapshot_append_iff counted file.bytes token (file, 5) 1 1 [] [0, 1]).mp contract).2
  obtain ⟨buffer, status, _⟩ := suffix.1
  change ReadReply.error .invalidRange = .ok buffer at status
  cases status

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks
