module

import Silmaril.Containers.SqliteVfs.FragmentContract.Thms
import Silmaril.Containers.SqliteVfs.Thms

namespace Silmaril.Containers.SqliteVfs.FragmentContract

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)

private def handle : Handle := ⟨0⟩
private def initial : FileState := ⟨[13], some .readOnly, 0⟩
private def counted : Handler (FileState × Nat) := fun state request =>
  let (reply, next) := readOnly 8 state.1 request
  (reply, next, state.2 + 1)
private def first : Exchange := ⟨.read handle 0 1, .ok [13]⟩
private def second : Exchange := ⟨.read handle 1 1, .shortRead [0]⟩
private def pending : Request := .read handle 2 0
private def events : List Event := encode [first, second] ++ [.recv pending]

private theorem read_backing_contract (snapshot : Bytes) (offset count : Nat) :
    ReadResult snapshot offset count (readBacking snapshot offset count) := by
  refine ⟨readBytes snapshot offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

private theorem observed : ∀ e ∈ completed events, ReplyMatchesSnapshot initial.bytes e := by
  intro exchange member
  change exchange ∈ [first, second] at member
  have either : exchange = first ∨ exchange = second := by simpa using member
  rcases either with rfl | rfl
  · exact ⟨by decide, by decide, read_backing_contract initial.bytes 0 1⟩
  · exact ⟨by decide, by decide, read_backing_contract initial.bytes 1 1⟩

example :
    ReadResult initial.bytes 0 2 (.shortRead [13, 0]) ∧
      (readFragments counted handle (initial, 5) 0 1 [1]).file = (initial, 7) := by
  have execution : (machine counted).Exec Mach.seqPolicy (.idle (initial, 5)) events
      (.pending (initial, 7) pending) :=
    exec_iff.mpr ⟨[first, second], (initial, 7), .cons rfl (.cons rfl (.nil _)),
      .inr ⟨pending, rfl, rfl⟩⟩
  obtain ⟨⟨reply, value, contract⟩, _, _⟩ :=
    observed_fragment_contract counted initial.bytes handle (initial, 5) 0 1 [1] events
      (.pending (initial, 7) pending) execution rfl observed
  change some (.shortRead [13, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨contract, rfl⟩

example : ¬ ReplyMatchesSnapshot initial.bytes
    ⟨.read handle 2 0, .error .invalidRange⟩ := by
  intro validReply
  obtain ⟨buffer, status, _⟩ := validReply.2.2
  change ReadReply.error .invalidRange = .shortRead buffer at status
  cases status

example : ¬ ReplyMatchesSnapshot initial.bytes
    ⟨.read handle (-1) 1, .ok [13]⟩ :=
  fun accepted => (by decide : ¬ (0 : Int) ≤ -1) accepted.1

example : ¬ ReplyMatchesSnapshot initial.bytes
    ⟨.read handle 0 (-1), .ok []⟩ :=
  fun accepted => (by decide : ¬ (0 : Int) ≤ -1) accepted.2.1

end Silmaril.Containers.SqliteVfs.FragmentContract
