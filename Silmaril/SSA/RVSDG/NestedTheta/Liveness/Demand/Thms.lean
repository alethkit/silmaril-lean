module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Correct
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Feedback
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Wiring

public section

namespace Silmaril.SSA.RVSDG.NestedTheta

open Silmaril.Semantics.Dataflow
open Liveness

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- Read comparison only requires agreement on valid user positions. -/
theorem Liveness.selectWires_compare {Ty : Type u} {entry users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires entry past users) {low high : Ty → Nat → Bool}
    (more : ∀ t i, i < users.length → low t i = true → high t i = true) :
    selectWires low wires ⊆ selectWires high wires :=
  Feedback.Proofs.selectWires_compare wires more

/-- Enlarging both the suffix demand and the child transfers enlarges the
read set, including through γ selection and the native θ iteration. -/
theorem Kind.demandReads_compare {ins out : Ports (PortType V S)} {past : List (Ports (PortType V S))}
    (kind : Kind Op ins out) (wires : Wires args past ins) (pc : Nat)
    {small large : List Address} (next : small ⊆ large)
    (low high : Fin kind.arity → Demand → List Address)
    (compare : ∀ i {a b}, (∀ p, a p = true → b p = true) → low i a ⊆ high i b) :
    kind.demandReads pc small wires low ⊆ kind.demandReads pc large wires high :=
  Feedback.Proofs.reads_compare kind wires pc next low high compare

/-- The bounded feedback iteration computes the least fixed point of the
body's demand transfer on the finite set of carried input positions. -/
theorem Term.feedbackLive_isLeast {carried : Ports (PortType V S)}
    (body : Term Op carried [] sigs (Theta.BodyResults carried)) (exit : Demand) :
    IsLeast {live | Feedback.step exit (fun demand => (body.demandPlan demand).live) live = live}
      (body.feedbackLive exit) :=
  Feedback.Proofs.feedback_isLeast body exit

/-- The executable analysis computes the shared least may solution at entry. -/
theorem Graph.mem_demandLiveIn_iff (g : Graph Op args [] sigs outs) (demand : Demand) (a : Address) :
    a ∈ g.demandLiveIn demand ↔ a ∈ (g.demandLiveness demand).mayOut 0 :=
  Demand.Proofs.mem_liveIn_iff g demand a

/-- With the same fuel, both inputs fail to return or return matching demanded
ports and exact state. The selected γ arm still executes at empty data demand. -/
theorem Graph.run_agrees_of_demand (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op) (fuel : Nat)
    (demand : Demand) (left right : Tuple m.Val args) (agree : g.AgreesOnDemandInputs demand left right) :
    demand.ResultAgrees (g.run m fuel left) (g.run m fuel right) :=
  Demand.Proofs.run_agrees g m fuel demand left right agree

/-- Every finite observation of the demanded ports and exact state transfers
in both directions. Undemanded output ports may vary. -/
theorem Graph.returnsDemand_iff (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (demand : Demand) (left right : Tuple m.Val args) (agree : g.AgreesOnDemandInputs demand left right)
    (expected : Tuple m.Val outs) :
    g.ReturnsDemand m demand left expected ↔ g.ReturnsDemand m demand right expected :=
  Demand.Proofs.returns_agree g m demand left right agree expected

/-- Agreement also preserves whether there is any finite return, including
for an empty demand on data output ports. -/
theorem Graph.hasFiniteReturn_iff_of_demand (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (demand : Demand) (left right : Tuple m.Val args) (agree : g.AgreesOnDemandInputs demand left right) :
    (∃ out, g.Returns m left out) ↔ ∃ out, g.Returns m right out :=
  Demand.Proofs.hasFiniteReturn_iff g m demand left right agree

end Silmaril.SSA.RVSDG.NestedTheta
