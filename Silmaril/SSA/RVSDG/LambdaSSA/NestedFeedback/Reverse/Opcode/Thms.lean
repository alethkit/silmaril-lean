module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Opcode.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Opcode

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

theorem opcode_injective {i o : Ports (OrderedRuntime.Structured.Ty τ)}
    (p q : Op Φ i o) (h : opcodeKey p = opcodeKey q) : p = q :=
  Proofs.opcode_injective p q h

abbrev opcodeCode : NestedTheta.Equality.OpcodeCode (Op (τ := τ) Φ) :=
  ⟨Key τ Φ, opcodeKey, opcode_injective⟩

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse
