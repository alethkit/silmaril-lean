module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs

/-! # Partial ordered actions on explicit token tuples -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial

open OrderedRuntime.Structured

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}}
variable {σ : Type (max u w)}

/-- Read only the live token from the input and restore the returned token
only if the ordered action succeeds. -/
def wireModel (m : OrderedRuntime.Structured.Model P E (StateT σ Part.{max u w})) :
    NestedTheta.Partial.Model.{u,max u v,max u w} (Opcode P E) where
  value := m.value
  snapshot _ := σ
  primitive
    | .ordered _ _ op, input =>
      let (data, token) := encode input
      Part.map decode ((m.step op data).run token)

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial
