module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs

/-! # Emit lambda-SSA from a preheader and header of ordered source quads -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA

open Diamond (ValueSort)
open Diamond.LambdaSSA (Primitive)
open Isotope.LambdaSSA (Region)

universe u v

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- Construct the loop graph from the source blocks, then use the generic
typed emitter to schedule its producers and pack the carried bank. -/
def lower (p : Program Op regs out) : Region (Primitive Op) :=
  SeaOfNodes.Loop.LambdaSSA.Generic.lower p.lower

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA
