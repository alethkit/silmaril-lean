module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Defs
public import Silmaril.SSA.RVSDG.Institution.Defs

/-! The native diamond equation signature and its generated γ graphs in the
existing RVSDG equation room. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG

open CategoryTheory

universe u v
variable {Data : Type u} {P Q : Signature.{u, v} Data}

/-- The #3135 opcode family, including its typed Boolean dispatch. RVSDG γ
is already a shape in this room's graph syntax. -/
def signature (P : Signature.{u, v} Data) :
    RVSDG.Institution.Signature.{u, max u v} (ValueSort Data) PEmpty.{u+1} :=
  ⟨Opcode P.op⟩

/-- Relabel native primitives at their existing profiles and fix dispatch. -/
def mapOpcode (h : P ⟶ Q) : RVSDG.Institution.OpcodeMap (Opcode P.op) (Opcode Q.op)
  | _, _, .pure op => .pure (Signature.Hom.opcode h op)
  | _, _, .dispatch out => .dispatch out

def mapSignature (h : P ⟶ Q) : signature P ⟶ signature Q :=
  ⟨mapOpcode h⟩

/-- Lower each side with the existing diamond lowering at the same value
boundary. The two vertex signatures include their respective dispatch and γ. -/
def lowerEquation (e : Equation P) : RVSDG.Institution.Equation (signature P).op :=
  ⟨dataPorts e.inputs, [.value e.out], _, _, e.lhs.lower, e.rhs.lower⟩

end Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG
