module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Proofs.Containers.SqliteVfs.FragmentPrefix.Trace

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.FragmentPrefix

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)

/-- The exact completed fragment schedule determines both alternating
transport events and the actual handler state, with an optional final receive. -/
theorem exec_fragment_prefix_iff {State : Type} (handler : Handler State)
    (handle : Handle) (start : State) (offset count : Nat) (rest : List Nat)
    (events : List Event) (finish : Phase State) :
    let result := readFragments handler handle start offset count rest
    ((machine handler).Exec Mach.seqPolicy (.idle start) events finish ∧
      (completed events).map Exchange.request = fragmentRequests handle offset (count :: rest)) ↔
    (events = encode result.trace ∧ finish = .idle result.file) ∨
      ∃ next, events = encode result.trace ++ [.recv next] ∧ finish = .pending result.file next :=
  Silmaril.Proofs.Containers.SqliteVfs.FragmentPrefix.exec_fragment_prefix_iff
    handler handle start offset count rest events finish

end Silmaril.Containers.SqliteVfs.FragmentPrefix
