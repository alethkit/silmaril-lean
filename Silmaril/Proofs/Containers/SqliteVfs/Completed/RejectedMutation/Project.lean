module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation.Defs
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation.Thms

public section

namespace Silmaril.Proofs.Containers.SqliteVfs.Completed.RejectedMutation

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.Completed
open Silmaril.Machine.SqliteVfs
open _root_.Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation (keep erase_rejected_mutations)

private theorem completed_pending (trace : Trace) (request : Request) :
    completed (encode trace ++ [.recv request]) = trace := by
  unfold completed
  rw [List.filterMap_append]
  change completed (encode trace) ++ [] = trace
  rw [List.append_nil, completed_encode]

/-- Filter rejected backing mutations from a valid logical execution,
preserving the exact ending phase, including any unanswered receive. -/
theorem execution_without_rejected_mutations {capacity : Nat} {step : Handler FileState}
    (law : BoundedWriteLaw capacity step id) {start : FileState}
    {events : List Event} {finish : Phase FileState}
    (run : (machine step).Exec Mach.seqPolicy (.idle start) events finish) :
    let trace := (completed events).filter keep
    let projected := match finish with
      | .idle _ => encode trace
      | .pending _ request => encode trace ++ [.recv request]
    (machine step).Exec Mach.seqPolicy (.idle start) projected finish ∧
      completed projected = trace := by
  obtain ⟨current, valid, phase⟩ := completed_exec_iff.mp run
  have stripped := erase_rejected_mutations law valid
  rcases phase with ⟨_, rfl⟩ | ⟨request, _, rfl⟩
  · exact ⟨exec_iff.mpr ⟨_, current, stripped, .inl ⟨rfl, rfl⟩⟩, completed_encode _⟩
  · exact ⟨exec_iff.mpr ⟨_, current, stripped, .inr ⟨request, rfl, rfl⟩⟩, completed_pending _ _⟩

end Silmaril.Proofs.Containers.SqliteVfs.Completed.RejectedMutation
