module

public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Theta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Defs

/-! Signature and sentence translation for the numbered pure loop lowering. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution

open CategoryTheory
open RVSDG.NestedTheta.Institution
open Diamond (ValueSort dataPorts)
open Diamond.Institution (mapDataflow)

universe u v

variable {Data : Type u} {P Q : Diamond.Institution.Signature.{u, v} Data}

/-- Lift opcode relabelling through the generated dialect, including the table
stored by the readback opcode. Routing retains exactly the same typed profile. -/
def opcodeMap (h : P ⟶ Q) :
    RVSDG.Institution.OpcodeMap (ThetaOpcode P.op) (ThetaOpcode Q.op)
  | _, _, .pure op => .pure (Diamond.Institution.Signature.Hom.opcode h op)
  | _, _, .route inputs carried => .route inputs carried
  | _, _, .readExit header result => .readExit (mapDataflow h header) result

/-- Both the source wires and the generated runtime use the same value sorts
and empty state alphabet. -/
abbrev target (P : Diamond.Institution.Signature.{u, v} Data) :
    RVSDG.Institution.Signature.{u, max u v} (ValueSort Data) PEmpty.{u + 1} :=
  ⟨ThetaOpcode P.op⟩

def signatureMap (h : P ⟶ Q) : target P ⟶ target Q :=
  ⟨opcodeMap h⟩

def lowerProgram {inputs : List (ValueSort Data)} {out : ValueSort Data}
    (p : Loop.Institution.Program P inputs out) :
    RuntimeObservation.Program (target P) (dataPorts inputs) [.value out] :=
  ⟨_, p.graph.lowerTheta⟩

/-- Translate each sentence to the same kind of partial observation on its
numbered θ graph. The source result becomes a singleton output tuple. -/
def translate : Loop.Institution.Sentence P → RuntimeObservation.Sentence (target P)
  | .equation e => .equation (lowerProgram e.lhs) (lowerProgram e.rhs)
  | .terminates p => .terminates (lowerProgram p)

end Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution
