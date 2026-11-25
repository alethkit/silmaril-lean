module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction.Trace

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction

open Silmaril.Machine.SqliteVfs

/-- A valid transcript of exactly the requested ordered fragments recovers
the same dependent exchange list and actual endpoint as the evaluator. -/
theorem read_fragments_reconstruct {State : Type} (step : Handler State)
    (handle : Handle) (state : State) (offset count : Nat) (rest : List Nat)
    {trace : Trace} {finish : State} (valid : Trace.Valid step state trace finish)
    (requests : trace.map Exchange.request = fragmentRequests handle offset (count :: rest)) :
    let result := readFragments step handle state offset count rest
    trace = result.trace ∧ finish = result.file :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction.read_fragments_reconstruct
    step handle state offset count rest valid requests

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction
