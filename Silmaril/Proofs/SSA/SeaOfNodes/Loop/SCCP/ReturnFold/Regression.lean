module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Example

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold

open Diamond.SCCP (TupleCovers)
open SCCP.Example (Byte entry facts)

-- The literal is the third header producer. The guard still reads producer 1.
example : resultProducer 0 .overdefined = .ok (some 2) := rfl
example : (withLiteral (graph 0) (.literal 0)).predicate.producer = some 1 := rfl
example : run 0 .overdefined false 0 = .ok (some 0) := rfl
example : run 0 .overdefined true 12 = .ok none := rfl

-- A widened return and an unseen exit take different rejection paths.
example : resultProducer 1 (.constant ⟨true⟩) = .error .overdefined := rfl
example : resultProducer 0 (.constant ⟨true⟩) = .error .unseen := rfl

private theorem stable_fold : fold 0 .overdefined = .ok (withLiteral (graph 0) (.literal 0)) := rfl

private theorem covered (enabled : Bool) : TupleCovers (facts 0 .overdefined) (entry 0 enabled) := by
  intro t port
  cases port with
  | head => rfl
  | tail p =>
    cases p with
    | head => exact True.intro
    | tail p => cases p

private theorem original_noReturn : ¬ ∃ result, (graph 0).Returns model (entry 0 true) result := by
  rintro ⟨result, returns⟩
  exact (graph 0).not_returns_of_backedge_invariant model (entry 0 true) result
    (fun old => old = (graph 0).initial model (entry 0 true)) rfl
    (by rintro _ rfl; exact ⟨_, rfl, rfl⟩) returns

-- The same admitted rewrite covers a returning input and a genuinely divergent one.
example : ¬ ∃ result, (withLiteral (graph 0) (.literal 0)).Returns model (entry 0 true) result :=
  (noFiniteReturn_iff stable_fold (covered true)).mpr original_noReturn

example (enabled : Bool) (budget : Nat) :
    (withLiteral (graph 0) (.literal 0)).evalBackedges model budget (entry 0 enabled) =
      (graph 0).evalBackedges model budget (entry 0 enabled) :=
  evalBackedges_eq stable_fold (covered enabled) budget

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold
