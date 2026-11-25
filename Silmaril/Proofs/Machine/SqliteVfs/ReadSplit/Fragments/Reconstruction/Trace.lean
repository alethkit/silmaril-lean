module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
  (fragmentRequests readFragments read_fragments_trace)

/-- The request list determines the dependent replies and final state of any
valid trace from the same starting state under a total handler. -/
private theorem valid_requests_unique {State : Type} {step : Handler State}
    {start firstEnd secondEnd : State} {first second : Trace}
    (firstValid : Trace.Valid step start first firstEnd)
    (secondValid : Trace.Valid step start second secondEnd)
    (requests : first.map Exchange.request = second.map Exchange.request) :
    first = second ∧ firstEnd = secondEnd := by
  induction firstValid generalizing second secondEnd with
  | nil =>
    cases secondValid with
    | nil => exact ⟨rfl, rfl⟩
    | cons => simp at requests
  | cons firstCall _ tailUnique =>
    cases secondValid with
    | nil => simp at requests
    | cons secondCall secondTail =>
      obtain ⟨rfl, sameRequests⟩ := List.cons.inj requests
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (firstCall.symm.trans secondCall)
      obtain ⟨rfl, rfl⟩ := tailUnique secondTail sameRequests
      exact ⟨rfl, rfl⟩

/-- A valid transcript of exactly the requested ordered fragments recovers
the same dependent exchange list and actual endpoint as the evaluator. -/
theorem read_fragments_reconstruct {State : Type} (step : Handler State)
    (handle : Handle) (state : State) (offset count : Nat) (rest : List Nat)
    {trace : Trace} {finish : State} (valid : Trace.Valid step state trace finish)
    (requests : trace.map Exchange.request = fragmentRequests handle offset (count :: rest)) :
    let result := readFragments step handle state offset count rest
    trace = result.trace ∧ finish = result.file := by
  obtain ⟨ranValid, ranRequests⟩ := read_fragments_trace step handle state offset count rest
  exact valid_requests_unique valid ranValid (requests.trans ranRequests.symm)

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction
