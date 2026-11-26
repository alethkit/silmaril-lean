module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Proofs.Containers.SqliteVfs.FragmentResume.Transition

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.FragmentResume

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit (combine)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)

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
      completed (events ++ [.send response]) = extended.trace :=
  Silmaril.Proofs.Containers.SqliteVfs.FragmentResume.complete_pending_fragment
    handler handle start offset count rest nextCount events

end Silmaril.Containers.SqliteVfs.FragmentResume
