module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Containers.SqliteVfs.FragmentContract.Reference.Thms
import Silmaril.Containers.SqliteVfs.FragmentContract.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Thms

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.FragmentContract.ContainedReplies

open Silmaril.Containers
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews readsSnapshot_of_agreeing_views)
open Silmaril.Containers.SqliteVfs.Completed (completed)

/-- A valid serial observation of the completed schedule inherits the
aggregate reference contract from agreement at its actual read calls. -/
theorem observed_of_agreeing_views {State : Type} (handler : Handler State)
    (reference : Bytes) (view : State → Bytes) (handle : Handle) (start : State) (offset count : Nat)
    (rest : List Nat) (events : List Event) (finish : Phase State)
    (execution : (machine handler).Exec Mach.seqPolicy (.idle start) events finish)
    (requests : (completed events).map Exchange.request = fragmentRequests handle offset (count :: rest))
    (agrees : ReadsAgreeingViews handler view reference handle start offset (count :: rest)) :
    let result := readFragments handler handle start offset count rest
    (∃ reply, result.reply = some reply ∧ ReadResult reference offset (count + rest.sum) reply) ∧
      completed events = result.trace ∧
      ((events = encode result.trace ∧ finish = .idle result.file) ∨
       ∃ next, events = encode result.trace ++ [.recv next] ∧ finish = .pending result.file next) :=
  observed_fragment_contract handler reference handle start offset count rest events finish execution requests
    (Reference.observed_replies_of_snapshot handler reference handle start offset (count :: rest)
      events finish execution requests
      (readsSnapshot_of_agreeing_views handler view reference handle start offset (count :: rest) agrees))

end Silmaril.Containers.SqliteVfs.FragmentContract.ContainedReplies
