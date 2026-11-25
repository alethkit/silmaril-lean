module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Opcode.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Opcode

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

theorem opcode_injective {i o : Ports (OrderedRuntime.Structured.Ty τ)}
    (p q : Wires.Op Φ i o) (h : opcodeKey p = opcodeKey q) : p = q :=
  Proofs.opcode_injective p q h

abbrev opcodeCode : NestedTheta.Equality.OpcodeCode (Wires.Op (τ := τ) Φ) :=
  ⟨OpcodeKey τ Φ, opcodeKey, opcode_injective⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize
