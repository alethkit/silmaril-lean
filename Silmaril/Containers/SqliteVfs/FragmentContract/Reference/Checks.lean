module

import Silmaril.Containers.SqliteVfs.FragmentContract.Reference.Thms
import Silmaril.Containers.SqliteVfs.FragmentContract.Thms
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Containers.SqliteVfs.FragmentPrefix.Thms

namespace Silmaril.Containers.SqliteVfs.FragmentContract.Reference

open Silmaril.Containers
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (ReadsSnapshot)
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot observed_fragment_contract)
open Silmaril.Containers.SqliteVfs.FragmentPrefix (exec_fragment_prefix_iff)

private def handle : Handle := ⟨0⟩
private def initial : FileState := ⟨[13], some .readOnly, 0⟩
private def changed : FileState := { initial with bytes := [90] }
private def updating : Handler (FileState × Nat) := fun state request =>
  let (reply, next) := readOnly 8 state.1 request
  (reply, { next with bytes := [90] }, state.2 + 1)
private def first : Exchange := ⟨.read handle 0 1, .ok [13]⟩
private def second : Exchange := ⟨.read handle 1 1, .shortRead [0]⟩
private def nextRead : Request := .read handle 2 0
private def actualEvents : List Event := encode [first, second] ++ [.recv nextRead]

private theorem read_backing_contract (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

example :
    (∀ e ∈ completed actualEvents, ReplyMatchesSnapshot initial.bytes e) ∧
      ReadResult initial.bytes 0 2 (.shortRead [13, 0]) ∧
      (machine updating).Exec Mach.seqPolicy (.idle (initial, 5)) actualEvents
        (.pending (changed, 7) nextRead) := by
  have run := (exec_fragment_prefix_iff updating handle (initial, 5) 0 1 [1] actualEvents
    (.pending (changed, 7) nextRead)).mpr (.inr ⟨nextRead, rfl, rfl⟩)
  have reads : ReadsSnapshot updating initial.bytes handle (initial, 5) 0 [1, 1] :=
    ⟨read_backing_contract initial.bytes 0 1, read_backing_contract initial.bytes 1 1, trivial⟩
  have checked := observed_replies_of_snapshot updating initial.bytes handle (initial, 5) 0 [1, 1]
    actualEvents (.pending (changed, 7) nextRead) run.1 run.2 reads
  obtain ⟨⟨reply, value, contract⟩, _, _⟩ := observed_fragment_contract updating initial.bytes handle
    (initial, 5) 0 1 [1] actualEvents (.pending (changed, 7) nextRead) run.1 run.2 checked
  change some (.shortRead [13, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨checked, contract, run.1⟩

example :
    (∀ e ∈ completed [.recv nextRead], ReplyMatchesSnapshot initial.bytes e) ∧
      (machine updating).Exec Mach.seqPolicy (.idle (initial, 5)) [.recv nextRead]
        (.pending (initial, 5) nextRead) := by
  have run : (machine updating).Exec Mach.seqPolicy (.idle (initial, 5)) [.recv nextRead]
      (.pending (initial, 5) nextRead) :=
    Completed.completed_exec_iff.mpr ⟨(initial, 5), .nil _, .inr ⟨nextRead, rfl, rfl⟩⟩
  exact ⟨observed_replies_of_snapshot updating initial.bytes handle (initial, 5) 2 []
    [.recv nextRead] (.pending (initial, 5) nextRead) run rfl trivial, run⟩

private def rejected : Exchange := ⟨nextRead, .error .invalidRange⟩

example :
    (machine updating).Exec Mach.seqPolicy (.idle (changed, 7)) (encode [rejected])
      (.idle (changed, 8)) ∧
    ¬ ReadsSnapshot updating initial.bytes handle (changed, 7) 2 [0] := by
  refine ⟨Completed.completed_exec_iff.mpr
    ⟨(changed, 8), .cons rfl (.nil _), .inl ⟨rfl, rfl⟩⟩, ?_⟩
  intro reads
  obtain ⟨buffer, status, _⟩ := reads.1
  change (ReadReply.error .invalidRange) = .shortRead buffer at status
  cases status

end Silmaril.Containers.SqliteVfs.FragmentContract.Reference
