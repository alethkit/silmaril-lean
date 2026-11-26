module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Petri.Order
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Firing.Proofs

open Relation (ReflTransGen)
open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Fire Finishes Marking pending)

variable {args : List ValueSort} {cells : Nat}

theorem activation_reachable (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) {mark : Marking (thetaRuntime cells) (.ofBase graph.thetaBody)}
    (trace : ReflTransGen
      (Fire (past := []) (thetaRuntime cells) (.ofBase graph.thetaBody) (encodeInput heap input) PUnit.unit)
      (pending (thetaRuntime cells) (.ofBase graph.thetaBody)) mark) :
    ∃ count, DonePrefix (thetaRuntime cells) (.ofBase graph.thetaBody) mark count := by
  induction trace with
  | refl => exact ⟨0, prefix_initial _ _⟩
  | tail _ step ih =>
    obtain ⟨count, ordered⟩ := ih
    exact ⟨count + 1, prefix_step (theta_chain graph) (encodeInput heap input) PUnit.unit ordered step⟩

set_option backward.isDefEq.respectTransparency false in
theorem activation_finishes (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (output : Tuple (WireVal cells) (RVSDG.Theta.BodyResults (carrier args))) :
    Finishes (thetaRuntime cells) graph.activation (encodeInput heap input) output ↔
      let body := graph.body.denote input heap
      Tuple.cons (F := WireVal cells) (t := .control 2)
        (continueTag body.1 (graph.stopWord input)) (encodeInput body.2 input) = output := by
  have run (fuel : Nat) :
      graph.activation.run (thetaRuntime cells) fuel (encodeInput heap input) =
        let body := graph.body.denote input heap
        some (.cons (continueTag body.1 (graph.stopWord input)) (encodeInput body.2 input)) := by
    rw [Graph.activation, ← RVSDG.NestedTheta.Graph.run_toTerm, RVSDG.NestedTheta.Term.toTerm_toGraph,
      RVSDG.NestedTheta.Term.run_ofBase, graph.thetaBody_run]
  rw [RVSDG.NestedTheta.Petri.finishes_iff]
  constructor
  · rintro ⟨fuel, observed⟩
    exact Option.some.inj ((run fuel).symm.trans observed)
  · intro eq
    exact ⟨0, (run 0).trans (congrArg some eq)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Firing.Proofs
