module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Defs

/-! # Checked forwarding within one ordered memory activation -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}

/-- Rewrite the native body at the checked input. The new body must still
admit a `Loop.Graph`, which requires a Load and a Store. The Store evidence
starts from an empty scan at each activation's table entry. -/
def rewrite (graph : Graph args) (candidate : Memory.Forwarding.Candidate)
    (certificate : Memory.Forwarding.Disjoint.Certificate args) (input : Tuple (Val cells) args) :
    Option (Graph args) :=
  match Memory.Forwarding.Disjoint.rewrite graph.body candidate certificate input with
  | none => none
  | some body =>
    if effects : accesses body = (true, true) then
      some ⟨body, effects, graph.stop⟩
    else none

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding
