module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation.Defs
import Silmaril.Proofs.Containers.SqliteVfs.Completed.RejectedMutation.Project

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.Completed.RejectedMutation

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.Completed
open Silmaril.Machine.SqliteVfs
open _root_.Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation (keep)

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
      completed projected = trace :=
  Proofs.Containers.SqliteVfs.Completed.RejectedMutation.execution_without_rejected_mutations
    law run

end Silmaril.Containers.SqliteVfs.Completed.RejectedMutation
