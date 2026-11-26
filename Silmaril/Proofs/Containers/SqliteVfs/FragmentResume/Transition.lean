module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Containers.SqliteVfs.FragmentPrefix.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.FragmentResume

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit (combine)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.Completed (completed_encode)
open Silmaril.Containers.SqliteVfs.FragmentPrefix (exec_fragment_prefix_iff)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks (read_fragments_chunks)

private theorem singleton_aggregate (previous : Option ReadReply) (next : ReadReply) :
    previous.bind (fun reply => (combine (.ok []) next).bind (combine reply)) =
      previous.bind (fun reply => combine reply next) := by
  cases previous with
  | none => rfl
  | some reply => cases next <;> cases reply <;> rfl

/-- Completing the unanswered next fragment sends the actual handler reply.
It extends the evaluator's trace, endpoint and optional aggregate by one call. -/
theorem complete_pending_fragment {State : Type} (handler : Handler State)
    (handle : Handle) (start : State) (offset count : Nat) (rest : List Nat) (nextCount : Nat)
    (events : List Event) :
    let before := readFragments handler handle start offset count rest
    let next : Request := .read handle (offset + count + rest.sum : Nat) nextCount
    let call := handler before.file next
    let response : Exchange := ⟨next, call.1⟩
    let extended := readFragments handler handle start offset count (rest ++ [nextCount])
    (machine handler).Exec Mach.seqPolicy (.idle start) events (.pending before.file next) →
    (completed events).map Exchange.request = fragmentRequests handle offset (count :: rest) →
    Step handler (.pending before.file next) (.ev (.send response)) (.idle call.2) ∧
      extended.trace = before.trace ++ [response] ∧ extended.file = call.2 ∧
      extended.reply = before.reply.bind (fun reply => combine reply call.1) ∧
      (machine handler).Exec Mach.seqPolicy (.idle start) (events ++ [.send response]) (.idle call.2) ∧
      completed (events ++ [.send response]) = extended.trace := by
  dsimp only
  intro execution requests
  let before := readFragments handler handle start offset count rest
  let next : Request := .read handle (offset + count + rest.sum : Nat) nextCount
  let call := handler before.file next
  let response : Exchange := ⟨next, call.1⟩
  let extended := readFragments handler handle start offset count (rest ++ [nextCount])
  have pendingEvents : events = encode before.trace ++ [.recv next] := by
    have shape := (exec_fragment_prefix_iff handler handle start offset count rest events
      (.pending before.file next)).mp ⟨execution, requests⟩
    rcases shape with ⟨_, phase⟩ | ⟨received, exactEvents, phase⟩
    · cases phase
    · have same := (Phase.pending.inj phase).2
      rw [same]
      exact exactEvents
  have chunked := read_fragments_chunks handler handle start offset count rest nextCount []
  change extended.file = call.2 ∧ extended.trace = before.trace ++ [response] ∧
    extended.reply = before.reply.bind (fun reply => (combine (.ok []) call.1).bind (combine reply)) at chunked
  obtain ⟨file, trace, reply⟩ := chunked
  have encoded : events ++ [.send response] = encode extended.trace := by
    simp [pendingEvents, trace, encode, List.flatMap_append, List.append_assoc, response]
  have resumed := (exec_fragment_prefix_iff handler handle start offset count (rest ++ [nextCount])
    (events ++ [.send response]) (.idle call.2)).mpr
      (.inl ⟨encoded, congrArg Phase.idle file.symm⟩)
  exact ⟨.send rfl, trace, file, reply.trans (singleton_aggregate _ _), resumed.1,
    by
      rw [encoded]
      exact completed_encode extended.trace⟩

end Silmaril.Proofs.Containers.SqliteVfs.FragmentResume
