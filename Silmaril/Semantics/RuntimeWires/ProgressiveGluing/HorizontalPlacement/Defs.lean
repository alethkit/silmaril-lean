module

public import Mathlib.Data.Fin.Embedding
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.FixedCapCategory.Defs

@[expose] public section

namespace Silmaril.RuntimeWires.ProgressiveGraph

/-- The strip occupied by the active operand. The idle strands occupy
the opposite open half of the square. -/
inductive ActiveStrip
  | left
  | right
  deriving DecidableEq

namespace ActiveStrip

def opposite : ActiveStrip → ActiveStrip
  | .left => .right
  | .right => .left

/-- Affine embedding of the horizontal coordinate into a half strip. -/
noncomputable def place (side : ActiveStrip) (x : ℝ) : ℝ :=
  match side with
  | .left => x / 2
  | .right => (1 + x) / 2

end ActiveStrip
end Silmaril.RuntimeWires.ProgressiveGraph
