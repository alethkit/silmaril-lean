module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Chunks.Composition

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.FragmentContract.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)

/-- Two valid observed chunks on the same reference snapshot recover the
aggregate contract and exact idle or pending state of their concatenation. -/
theorem observed_fragment_chunks {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start middle : State)
    (offset firstCount : Nat) (firstRest : List Nat) (secondCount : Nat) (secondRest : List Nat)
    (left right : List Event) (finish : Phase State)
    (leftExec : (machine handler).Exec Mach.seqPolicy (.idle start) left (.idle middle))
    (leftOrder : (completed left).map Exchange.request = fragmentRequests handle offset (firstCount :: firstRest))
    (leftReplies : ∀ e ∈ completed left, ReplyMatchesSnapshot snapshot e)
    (rightExec : (machine handler).Exec Mach.seqPolicy (.idle middle) right finish)
    (rightOrder : (completed right).map Exchange.request =
      fragmentRequests handle (offset + firstCount + firstRest.sum) (secondCount :: secondRest))
    (rightReplies : ∀ e ∈ completed right, ReplyMatchesSnapshot snapshot e) :
    let rest := firstRest ++ (secondCount :: secondRest)
    let result := readFragments handler handle start offset firstCount rest
    (machine handler).Exec Mach.seqPolicy (.idle start) (left ++ right) finish ∧
      completed (left ++ right) = result.trace ∧
      (∃ reply, result.reply = some reply ∧ ReadResult snapshot offset (firstCount + rest.sum) reply) ∧
      ((left ++ right = encode result.trace ∧ finish = .idle result.file) ∨
       ∃ next, left ++ right = encode result.trace ++ [.recv next] ∧ finish = .pending result.file next) :=
  Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Chunks.observed_fragment_chunks
    handler snapshot handle start middle offset firstCount firstRest secondCount secondRest
    left right finish leftExec leftOrder leftReplies rightExec rightOrder rightReplies

end Silmaril.Containers.SqliteVfs.FragmentContract.Chunks
