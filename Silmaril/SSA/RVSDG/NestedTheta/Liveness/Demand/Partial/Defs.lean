module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Defs

/-! # Demand observations for nested partial primitives -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial

open OrderedRuntime.Structured (Ty Opcode)
open ExplicitRuntime.Partial (wireModel)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}

/-- A finite return of the demanded data positions and every returned state
port in the existing partial wire semantics. -/
def ReturnsDemand (m : ExplicitRuntime.Partial.Model.{u,v,w} P E σ) (g : Graph (Opcode P E) args [] sigs outs)
    (demand : Demand) (input : Tuple (wireModel m).Val args)
    (expected : Tuple (wireModel m).Val outs) : Prop :=
  ∃ output, NestedTheta.Partial.returns (wireModel m) g input output ∧ demand.Agrees output expected

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial
