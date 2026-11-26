module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Defs

/-! Signature and sentence translation for the scoped diamond lowering.
The model comparison uses the scoped model induced by a total diamond model. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution

open CategoryTheory

variable {Data : Type} {P Q : Diamond.Institution.Signature.{0, 0} Data}

/-- Lift a native opcode map to the diamond's RVSDG dialect, fixing dispatch. -/
def opcodeMap (h : P ⟶ Q) : RVSDG.Institution.OpcodeMap (Opcode P.op) (Opcode Q.op)
  | _, _, .pure op => .pure (Diamond.Institution.Signature.Hom.opcode h op)
  | _, _, .dispatch out => .dispatch out

/-- The profile-preserving morphism between the generated RVSDG signatures. -/
def rvsdgMap (h : P ⟶ Q) : source P.op ⟶ source Q.op :=
  ⟨opcodeMap h⟩

/-- The isolated project dialect generated from the source signature. -/
abbrev target (P : Diamond.Institution.Signature.{0, 0} Data) : Silmaril.MLIR.Institution.Signature true :=
  RVSDG.MLIR.Graph.signature (source P.op)

/-- Relabel scoped MLIR symbols while retaining their full typed profiles. -/
abbrev scopedMap (h : P ⟶ Q) : target P ⟶ target Q :=
  RVSDG.MLIR.Graph.mapSignature (rvsdgMap h)

/-- Translate a native equation by lowering its two graphs. -/
def translate (e : Diamond.Institution.Equation P) : Silmaril.MLIR.Institution.Equation (target P) :=
  lowerEquation e.lhs e.rhs

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution
