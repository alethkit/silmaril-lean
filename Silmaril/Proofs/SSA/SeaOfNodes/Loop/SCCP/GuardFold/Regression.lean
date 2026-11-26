module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Example

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold

open Diamond.SCCP (TupleCovers)
open SCCP.Example (Byte entry facts)

example : predicateProducer (.constant ⟨false⟩) = .ok (some 1) := rfl
example : predicateProducer (.constant ⟨true⟩) = .ok (some 1) := rfl
example : run false 0 = .ok (some 0) := rfl
example : run true 12 = .ok none := rfl

example : (SCCP.solve model graph (facts 0 (.constant ⟨false⟩))).1 =
    {incomingIndex .entry, exitIndex} := rfl
example : (SCCP.solve model graph (facts 0 (.constant ⟨true⟩))).1 =
    {incomingIndex .entry, incomingIndex .backedge} := rfl

-- An unseen guard leaves neither tail successor marked.
example : (SCCP.solve model graph (facts 0 .bottom)).1 = {incomingIndex .entry} := rfl
example : predicateProducer .bottom = .error .unseen := rfl

-- Two possible successors and a guard that varies over a run both refuse.
example : predicateProducer .overdefined = .error .overdefined := rfl
example : varyingGuard = .error .overdefined := rfl

private theorem accepted (test : Bool) :
    fold (.constant ⟨test⟩) = .ok (withLiteral graph (.test test)) := by
  cases test <;> rfl

private theorem covered (test : Bool) : TupleCovers (facts 0 (.constant ⟨test⟩)) (entry 0 test) := by
  intro t port
  cases port with
  | head => rfl
  | tail p =>
    cases p with
    | head => rfl
    | tail p => cases p

private theorem original_noReturn : ¬ ∃ result, graph.Returns model (entry 0 true) result := by
  rintro ⟨result, returned⟩
  exact graph.not_returns_of_backedge_invariant model (entry 0 true) result (fun _ => True) trivial
    (fun _ _ => ⟨.cons (1 : Byte) .nil, rfl, trivial⟩) returned

example : ¬ ∃ result, (withLiteral graph (.test true)).Returns model (entry 0 true) result :=
  (noFiniteReturn_iff (accepted true) (covered true)).mpr original_noReturn

example (budget : Nat) : (withLiteral graph (.test true)).evalBackedges model budget (entry 0 true) = none := by
  rw [evalBackedges_eq (accepted true) (covered true)]
  cases observed : graph.evalBackedges model budget (entry 0 true) with
  | none => rfl
  | some result =>
    exact (original_noReturn ⟨result, (graph.returns_iff_evalBackedges model (entry 0 true) result).mpr
      ⟨budget, observed⟩⟩).elim

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold
