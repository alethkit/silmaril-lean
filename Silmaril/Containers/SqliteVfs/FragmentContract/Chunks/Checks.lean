module

import Silmaril.Containers.SqliteVfs.FragmentContract.Chunks.Thms
import Silmaril.Containers.SqliteVfs.FragmentPrefix.Thms

namespace Silmaril.Containers.SqliteVfs.FragmentContract.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)
open Silmaril.Containers.SqliteVfs.FragmentPrefix (exec_fragment_prefix_iff)

private def handle : Handle := ⟨0⟩
private def initial : FileState := ⟨[13], some .readOnly, 0⟩
private def counted : Handler (FileState × Nat) := fun state request =>
  let (reply, next) := readOnly 8 state.1 request
  (reply, next, state.2 + 1)
private def first : Exchange := ⟨.read handle 0 1, .ok [13]⟩
private def second : Exchange := ⟨.read handle 1 1, .shortRead [0]⟩
private def nextRead : Request := .read handle 2 0
private def left : List Event := encode [first]
private def right : List Event := encode [second] ++ [.recv nextRead]

private theorem read_backing_contract (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

private theorem checkedSingleton {events : List Event} {exchange : Exchange}
    (projection : completed events = [exchange])
    (contract : ReplyMatchesSnapshot initial.bytes exchange) :
    ∀ e ∈ completed events, ReplyMatchesSnapshot initial.bytes e := by
  intro e member
  rw [projection, List.mem_singleton] at member
  subst e
  exact contract

private theorem firstContract : ReplyMatchesSnapshot initial.bytes first :=
  ⟨by decide, by decide, read_backing_contract initial.bytes 0 1⟩

private theorem secondContract : ReplyMatchesSnapshot initial.bytes second :=
  ⟨by decide, by decide, read_backing_contract initial.bytes 1 1⟩

example :
    ReadResult initial.bytes 0 2 (.shortRead [13, 0]) ∧
      (machine counted).Exec Mach.seqPolicy (.idle (initial, 5)) (left ++ right)
        (.pending (initial, 7) nextRead) ∧ completed (left ++ right) = [first, second] := by
  have before := (exec_fragment_prefix_iff counted handle (initial, 5) 0 1 [] left
    (.idle (initial, 6))).mpr (.inl ⟨rfl, rfl⟩)
  have after := (exec_fragment_prefix_iff counted handle (initial, 6) 1 1 [] right
    (.pending (initial, 7) nextRead)).mpr (.inr ⟨nextRead, rfl, rfl⟩)
  obtain ⟨run, projection, ⟨reply, value, contract⟩, _⟩ := observed_fragment_chunks counted
    initial.bytes handle (initial, 5) (initial, 6) 0 1 [] 1 [] left right
    (.pending (initial, 7) nextRead) before.1 before.2 (checkedSingleton rfl firstContract)
    after.1 after.2 (checkedSingleton rfl secondContract)
  change some (.shortRead [13, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨contract, run, projection⟩

example :
    let rightDone := encode [second]
    (machine counted).Exec Mach.seqPolicy (.idle (initial, 5)) (left ++ rightDone)
        (.idle (initial, 7)) ∧
      completed (left ++ rightDone) = [first, second] ∧
      left ++ rightDone = encode [first, second] := by
  let rightDone := encode [second]
  have before := (exec_fragment_prefix_iff counted handle (initial, 5) 0 1 [] left
    (.idle (initial, 6))).mpr (.inl ⟨rfl, rfl⟩)
  have after := (exec_fragment_prefix_iff counted handle (initial, 6) 1 1 [] rightDone
    (.idle (initial, 7))).mpr (.inl ⟨rfl, rfl⟩)
  obtain ⟨run, projection, _, shape⟩ := observed_fragment_chunks counted
    initial.bytes handle (initial, 5) (initial, 6) 0 1 [] 1 [] left rightDone
    (.idle (initial, 7)) before.1 before.2 (checkedSingleton rfl firstContract)
    after.1 after.2 (checkedSingleton rfl secondContract)
  rcases shape with ⟨events, _⟩ | ⟨_, _, phase⟩
  · exact ⟨run, projection, events⟩
  · cases phase

end Silmaril.Containers.SqliteVfs.FragmentContract.Chunks
