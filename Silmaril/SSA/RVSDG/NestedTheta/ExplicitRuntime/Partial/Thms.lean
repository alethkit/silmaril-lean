module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Agreement

/-! # Successful observations of partial ordered actions -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial

open OrderedRuntime.Structured

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}}
variable {σ : Type (max u w)} {ins outs : Ports (OrderedRuntime.Structured.Ty V)}

/-- A successful explicit primitive observation matches the ordered action
on every data port and on the returned token. -/
theorem primitive_mem_iff (m : OrderedRuntime.Structured.Model P E (StateT σ Part.{max u w}))
    (i : Data ins) (o : Data outs) (op : Instruction P E ins outs)
    (input : Tuple (RuntimeValues m.value σ) (Threaded ins))
    (output : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    output ∈ (wireModel m).primitive (.ordered i o op) input ↔
      encode output ∈ ((m.step op (encode input).1).run (encode input).2) :=
  Proofs.primitive_mem m i o op input output

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial
