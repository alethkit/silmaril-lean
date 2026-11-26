module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs

/-! # Emit the validated smaller carried bank as a typed λSSA CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA

open Diamond (ValueSort)
open Diamond.LambdaSSA (Primitive)
open Isotope.LambdaSSA (Region)

universe u v

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- Emit the pruned CFG when the source-derived carried mask is accepted. -/
def lower (p : Program Op regs out) : Option (Region (Primitive Op)) :=
  (prune p).map SeaOfNodes.Loop.LambdaSSA.Generic.lower

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA
