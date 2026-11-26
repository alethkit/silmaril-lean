module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Defs

/-! # Checked forwarding within one ordered memory activation -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}

/-- Rewrite the native body under the certificate's input assumptions. The
new body must still admit a `Loop.Graph`, which requires a Load and a Store. -/
def rewriteWith (graph : Graph args) (candidate : Memory.Forwarding.Candidate)
    (certificate : Memory.Forwarding.Disjoint.Certificate args) : Option (Graph args) :=
  match Memory.Forwarding.Disjoint.rewriteWith graph.body candidate certificate with
  | none => none
  | some body =>
    if effects : accesses body = (true, true) then
      some ⟨body, effects, graph.stop⟩
    else none

/-- Validate the assumptions at the invocation before returning the rewrite. -/
def rewrite (graph : Graph args) (candidate : Memory.Forwarding.Candidate)
    (certificate : Memory.Forwarding.Disjoint.Certificate args) (input : Tuple (Val cells) args) :
    Option (Graph args) :=
  if certificate.check input then rewriteWith graph candidate certificate else none

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding
