module

import Silmaril.Containers.SqliteVfs.FragmentContract.Resume.Thms
import Silmaril.Containers.SqliteVfs.FragmentPrefix.Thms
import Silmaril.Containers.SqliteVfs.FragmentResume.Thms

namespace Silmaril.Containers.SqliteVfs.FragmentContract.Resume

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)
open Silmaril.Containers.SqliteVfs.FragmentPrefix (exec_fragment_prefix_iff)
open Silmaril.Containers.SqliteVfs.FragmentResume (complete_pending_fragment)

private def handle : Handle := ⟨0⟩
private def initial : FileState := ⟨[7], some .readOnly, 0⟩
private def counted : Handler (FileState × Nat) := fun state request =>
  let (reply, next) := readOnly 8 state.1 request
  (reply, next, state.2 + 1)
private def first : Exchange := ⟨.read handle 0 1, .ok [7]⟩
private def beyond : Request := .read handle 1 2
private def eofEvents : List Event := encode [first] ++ [.recv beyond]

private theorem read_backing_contract (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

example :
    ReadResult initial.bytes 0 3 (.shortRead [7, 0, 0]) ∧
      (machine counted).Exec Mach.seqPolicy (.idle (initial, 5))
        (eofEvents ++ [.send ⟨beyond, .shortRead [0, 0]⟩]) (.idle (initial, 7)) := by
  have pending := (exec_fragment_prefix_iff counted handle (initial, 5) 0 1 [] eofEvents
    (.pending (initial, 6) beyond)).mpr (.inr ⟨beyond, rfl, rfl⟩)
  have prefixReplies : ∀ e ∈ completed eofEvents, ReplyMatchesSnapshot initial.bytes e := by
    intro e member
    change e ∈ [first] at member
    have equal : e = first := by simpa using member
    subst e
    exact ⟨by decide, by decide, read_backing_contract initial.bytes 0 1⟩
  have sent : ReplyMatchesSnapshot initial.bytes ⟨beyond, .shortRead [0, 0]⟩ :=
    ⟨by decide, by decide, read_backing_contract initial.bytes 1 2⟩
  obtain ⟨⟨reply, value, contract⟩, _, _, run⟩ :=
    complete_pending_fragment_contract counted initial.bytes handle (initial, 5) 0 1 [] 2 eofEvents
      pending.1 pending.2 prefixReplies sent
  change some (.shortRead [7, 0, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨contract, run⟩

private def rejected : Request := .read handle 1 0
private def badEvents : List Event := encode [first] ++ [.recv rejected]

example :
    ¬ ReplyMatchesSnapshot initial.bytes ⟨rejected, .error .invalidRange⟩ ∧
      (machine counted).Exec Mach.seqPolicy (.idle (initial, 5))
        (badEvents ++ [.send ⟨rejected, .error .invalidRange⟩]) (.idle (initial, 7)) := by
  have pending := (exec_fragment_prefix_iff counted handle (initial, 5) 0 1 [] badEvents
    (.pending (initial, 6) rejected)).mpr (.inr ⟨rejected, rfl, rfl⟩)
  refine ⟨?_, (complete_pending_fragment counted handle (initial, 5) 0 1 [] 0 badEvents
    pending.1 pending.2).2.2.2.2.1⟩
  intro checked
  obtain ⟨buffer, status, _⟩ := checked.2.2
  change ReadReply.error .invalidRange = .ok buffer at status
  cases status

end Silmaril.Containers.SqliteVfs.FragmentContract.Resume
