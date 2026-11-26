module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Correct

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial

open OrderedRuntime.Structured (Ty Opcode)
open ExplicitRuntime.Partial (Observation wireModel abnormal)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}

/-- Live input agreement preserves and reflects finite returns at the
requested data ports and every returned state port. -/
theorem returnsDemand_iff (m : ExplicitRuntime.Partial.Model.{u,v,w} P E σ) (g : Graph (Opcode P E) args [] sigs outs)
    (demand : Demand) (left right : Tuple (wireModel m).Val args)
    (agree : g.AgreesOnDemandInputs demand left right) (expected : Tuple (wireModel m).Val outs) :
    ReturnsDemand m g demand left expected ↔ ReturnsDemand m g demand right expected :=
  Proofs.returnsDemand_iff m g demand left right agree expected

/-- The same exact abnormal observation is possible on either input.
A block keeps its nested site, typed opcode and operands, and attempt
state. The diverging case matches actual productive restart traces. -/
theorem abnormal_iff_of_live (m : ExplicitRuntime.Partial.Model.{u,v,w} P E σ) (g : Graph (Opcode P E) args [] sigs outs)
    (demand : Demand) (left right : Tuple (wireModel m).Val args)
    (agree : g.AgreesOnDemandInputs demand left right) (obs : Observation m) :
    abnormal m g left obs ↔ abnormal m g right obs :=
  Proofs.abnormal_iff m g demand left right agree obs

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial
