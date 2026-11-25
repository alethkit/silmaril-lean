module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.FragmentPrefix

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.Completed
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction (read_fragments_reconstruct)

private theorem completed_append_recv (events : List Event) (request : Request) :
    completed (events ++ [.recv request]) = completed events := by
  simp [completed, List.filterMap_append]

/-- The exact completed fragment schedule determines both alternating
transport events and the actual handler state, with an optional final receive. -/
theorem exec_fragment_prefix_iff {State : Type} (handler : Handler State)
    (handle : Handle) (start : State) (offset count : Nat) (rest : List Nat)
    (events : List Event) (finish : Phase State) :
    let result := readFragments handler handle start offset count rest
    ((machine handler).Exec Mach.seqPolicy (.idle start) events finish ∧
      (completed events).map Exchange.request = fragmentRequests handle offset (count :: rest)) ↔
    (events = encode result.trace ∧ finish = .idle result.file) ∨
      ∃ next, events = encode result.trace ++ [.recv next] ∧ finish = .pending result.file next := by
  dsimp only
  constructor
  · intro ⟨execution, requests⟩
    obtain ⟨returned, valid, shape⟩ := completed_exec_iff.mp execution
    obtain ⟨exchanges, state⟩ :=
      read_fragments_reconstruct handler handle start offset count rest valid requests
    rw [exchanges, state] at shape
    exact shape
  · intro shape
    let result := readFragments handler handle start offset count rest
    have projection : completed events = result.trace := by
      rcases shape with ⟨rfl, _⟩ | ⟨next, rfl, _⟩
      · exact completed_encode _
      · rw [completed_append_recv, completed_encode]
    obtain ⟨valid, requests⟩ := read_fragments_trace handler handle start offset count rest
    refine ⟨completed_exec_iff.mpr ⟨result.file, ?_, ?_⟩, ?_⟩
    · rw [projection]
      exact valid
    · rw [projection]
      exact shape
    · rw [projection]
      exact requests

end Silmaril.Proofs.Containers.SqliteVfs.FragmentPrefix
