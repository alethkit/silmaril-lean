module

public import Silmaril.SSA.SeaOfNodes.Pure.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-! # Eliminate a trivial φ from the pure Sea of Nodes diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.PhiElim

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}

/-- When both predecessor slots name the same wire address, keep the
producer table and return that wire in a straight-line program. -/
def eliminate (g : Graph Op inputs sigs out) : Option (Pure.Program Op inputs out) :=
  if (g.phi.operand .first).address = (g.phi.operand .second).address then
    some { dataflow := g.dataflow, result := g.phi.operand .first }
  else none

end Silmaril.SSA.SeaOfNodes.Diamond.PhiElim
