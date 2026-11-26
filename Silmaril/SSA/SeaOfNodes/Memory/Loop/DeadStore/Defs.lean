module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs

/-! # Delete a Store overwritten within the same loop activation -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore

open RVSDG (Tuple)
open Memory.DeadStore (Candidate)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

/-- Both Store versions are in the original activation table. The
straight-line checker must find the overwrite before that table's Return. -/
def rewriteWith (graph : Graph args) (candidate : Candidate) (facts : Certificate args) :
    Option (Graph args) := do
  let body ← Memory.DeadStore.rewriteWith graph.body candidate facts
  if effects : accesses body = (true, true) then
    some ⟨body, effects, graph.stop⟩
  else none

/-- Validate the concrete cell inequalities on the invariant input tuple. -/
def rewrite (graph : Graph args) (candidate : Candidate) (facts : Certificate args)
    (input : Tuple (Val cells) args) : Option (Graph args) :=
  if facts.check input then rewriteWith graph candidate facts else none

end Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore
