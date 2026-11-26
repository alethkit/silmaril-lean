module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Containers.SqliteVfs.FragmentContract.Thms
import Silmaril.Containers.SqliteVfs.FragmentPrefix.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)
open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.FragmentContract (observed_fragment_contract)
open Silmaril.Containers.SqliteVfs.FragmentPrefix (exec_fragment_prefix_iff)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks (read_fragments_chunks)

private theorem completed_append (left right : List Event) :
    completed (left ++ right) = completed left ++ completed right := by
  simp [completed, List.filterMap_append]

private theorem encode_append (left right : Trace) :
    encode (left ++ right) = encode left ++ encode right := by
  simp [encode, List.flatMap_append]

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
       ∃ next, left ++ right = encode result.trace ++ [.recv next] ∧ finish = .pending result.file next) := by
  dsimp only
  let first := readFragments handler handle start offset firstCount firstRest
  let second := readFragments handler handle first.file (offset + firstCount + firstRest.sum)
    secondCount secondRest
  let both := readFragments handler handle start offset firstCount (firstRest ++ (secondCount :: secondRest))
  have ⟨leftEvents, middleEq⟩ : left = encode first.trace ∧ middle = first.file := by
    have shape := (exec_fragment_prefix_iff handler handle start offset firstCount firstRest
      left (.idle middle)).mp ⟨leftExec, leftOrder⟩
    rcases shape with ⟨events, phase⟩ | ⟨next, _, phase⟩
    · exact ⟨events, Phase.idle.inj phase⟩
    · cases phase
  subst middle
  have rightShape := (exec_fragment_prefix_iff handler handle first.file
    (offset + firstCount + firstRest.sum) secondCount secondRest right finish).mp ⟨rightExec, rightOrder⟩
  obtain ⟨file, trace, _⟩ :=
    read_fragments_chunks handler handle start offset firstCount firstRest secondCount secondRest
  change both.file = second.file at file
  change both.trace = first.trace ++ second.trace at trace
  have joinedShape : (left ++ right = encode both.trace ∧ finish = .idle both.file) ∨
      ∃ next, left ++ right = encode both.trace ++ [.recv next] ∧ finish = .pending both.file next := by
    rw [file, trace, encode_append, leftEvents]
    rcases rightShape with ⟨events, phase⟩ | ⟨next, events, phase⟩
    · exact .inl ⟨by rw [events], phase⟩
    · exact .inr ⟨next, by rw [events, List.append_assoc], phase⟩
  obtain ⟨execution, order⟩ := (exec_fragment_prefix_iff handler handle start offset firstCount
    (firstRest ++ (secondCount :: secondRest)) (left ++ right) finish).mpr joinedShape
  have joinedReplies : ∀ e ∈ completed (left ++ right), ReplyMatchesSnapshot snapshot e := by
    intro e member
    rw [completed_append, List.mem_append] at member
    exact member.elim (leftReplies e) (rightReplies e)
  obtain ⟨aggregate, projection, shape⟩ := observed_fragment_contract handler snapshot handle start
    offset firstCount (firstRest ++ (secondCount :: secondRest)) (left ++ right) finish execution order joinedReplies
  exact ⟨execution, projection, aggregate, shape⟩

end Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Chunks
