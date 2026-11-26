module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # Link the first diamond's exit to the second diamond's entry -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA

open Diamond.LambdaSSA (Primitive)
open Arms.LambdaSSA (armTerminator resultCode)
open Loop.LambdaSSA.Generic (unpack)
open Silmaril.Isotope.LambdaSSA (Region)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs middle results : List (ValueSort Data)}
variable {firstSigs secondSigs : List (List (Ty Data))}
variable (g : Graph Op inputs middle results firstSigs secondSigs)

/-- A join edge carries its CFG scope as well as its original predecessor
and successor occurrence. The two joins each have their own local label two. -/
abbrev JoinEdge :=
  Sum (PhiView.EdgeOcc (armTerminator g.first)) (PhiView.EdgeOcc (armTerminator g.second))

/-- Look up the original occurrence using that stage's predecessor order. -/
def edge : Stage → Slot → JoinEdge g
  | .first, slot => .inl (Arms.LambdaSSA.edge g.first slot)
  | .second, slot => .inr (Arms.LambdaSSA.edge g.second slot)

def edgeProjection (occurrence : JoinEdge g) : Projection :=
  occurrence.elim PhiView.EdgeOcc.source PhiView.EdgeOcc.source

/-- After splitting a right-associated packet, the component at position
`i` sits behind two binders per remaining component. Free indices beyond
the input context map to the terminal unit. -/
def inputIndex (size i : Nat) : Nat :=
  if i < size then 2 * (size - i) - 1 else 0

/-- Destructure a packed input once and place the region's free variables
at the decoded bindings. -/
def fromPacked (input : List (ValueSort Data)) (r : Region (Primitive Op)) : Region (Primitive Op) :=
  unpack (dataPorts input) (r.renameVars (inputIndex input.length))

/-- Connect a single packed exit to a region whose whole input is that tuple. -/
def link (middle : List (ValueSort Data)) (first after : Region (Primitive Op)) :
    Region (Primitive Op) :=
  first.linkExits [resultCode middle] (fun _ => fromPacked middle after)

/-- The sole link block receives the first result as a single parameter. -/
def continuation : Region (Primitive Op) := fromPacked middle (Arms.LambdaSSA.lower g.second)

/-- The canonical linked CFG binds the first exit's payload and runs the
second region as its sole local continuation. -/
def lower : Region (Primitive Op) :=
  link middle (Arms.LambdaSSA.lower g.first) (Arms.LambdaSSA.lower g.second)

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA
