module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Defs
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Proofs

open OrderedRuntime.Structured

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}}
variable {σ : Type (max u w)} {ins outs : Ports (OrderedRuntime.Structured.Ty V)}

theorem primitive_mem (m : OrderedRuntime.Structured.Model P E (StateT σ Part.{max u w}))
    (i : Data ins) (o : Data outs) (op : Instruction P E ins outs)
    (input : Tuple (RuntimeValues m.value σ) (Threaded ins))
    (output : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    output ∈ (wireModel m).primitive (.ordered i o op) input ↔
      encode output ∈ ((m.step op (encode input).1).run (encode input).2) := by
  change output ∈ Part.map decode _ ↔ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨result, returned, rfl⟩
    rwa [encode_decode result]
  · intro returned
    exact ⟨encode output, returned, decode_encode o output⟩

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Proofs
