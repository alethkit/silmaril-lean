module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Opcode.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Decision.Defs

/-! # Certify the candidate against the actual numbered graph -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A I M E D : τ}

structure Match (g : Graph Φ A I M E D) where
  components : Components Φ A I M E D
  wiring : components.graph = g

def Match.recover {g : Graph Φ A I M E D} (result : Match g) : Fragment Φ A E D :=
  Source result.components.first result.components.second

variable [DecidableEq τ] [DecidableEq Φ]

deriving instance DecidableEq for PortType

/-- The executable recognizer compares the reconstructed graph against
the original, including port sorts, route annotations, and every address. -/
def certify (g : Graph Φ A I M E D) (components : Components Φ A I M E D) : Option (Match g) :=
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) components.graph g
  if same : components.graph = g then some ⟨components, same⟩ else none

/-- There is one admitted cut. Inside a body, the parser chooses
right-associated sequencing and certifies the resulting wiring. -/
def recognize (g : Graph Φ A I M E D) : Option (Match g) :=
  (candidate g).bind (certify g)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize
