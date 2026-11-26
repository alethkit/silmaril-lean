module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Example

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold

open Diamond.SCCP (TupleCovers)
open SCCP.Example (Byte entry facts)
open ReturnFold.Example (model literals)
open Semantics.Dataflow (Flat)

-- The backedge supplies one, even though the entry supplies zero and the Phi widens.
example : feedbackFact model graph (facts 0 .overdefined) .head = .constant (1 : Byte) := rfl
example : (SCCP.solve model graph (facts 0 .overdefined)).2.1 (0 : Fin 1) = (.overdefined : Flat Byte) := rfl
example : feedbackProducer = .ok (some 1) := rfl
example : run false 0 = .ok (some 0) := rfl

-- A changing feedback expression widens. A disabled edge supplies no evidence.
example : refusal true = .error .overdefined := rfl
example : refusal false = .error .unseen := rfl

private theorem accepted : fold = .ok (withLiteral graph .head (.literal 1)) := rfl

private theorem covered (enabled : Bool) : TupleCovers (facts 0 .overdefined) (entry 0 enabled) := by
  intro t port
  cases port with
  | head => rfl
  | tail p =>
    cases p with
    | head => exact True.intro
    | tail p => cases p

private theorem original_noReturn : ¬ ∃ result, graph.Returns model (entry 0 true) result := by
  rintro ⟨result, returned⟩
  exact graph.not_returns_of_backedge_invariant model (entry 0 true) result (fun _ => True) trivial
    (fun _ _ => ⟨.cons (1 : Byte) .nil, rfl, trivial⟩) returned

example : ¬ ∃ result, (withLiteral graph .head (.literal 1)).Returns model (entry 0 true) result :=
  (noFiniteReturn_iff accepted (covered true)).mpr original_noReturn

example (budget : Nat) :
    (withLiteral graph .head (.literal 1)).evalBackedges model budget (entry 0 true) = none := by
  rw [evalBackedges_eq accepted (covered true)]
  cases observed : graph.evalBackedges model budget (entry 0 true) with
  | none => rfl
  | some result =>
    exact (original_noReturn ⟨result, (graph.returns_iff_evalBackedges model (entry 0 true) result).mpr
      ⟨budget, observed⟩⟩).elim

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold
