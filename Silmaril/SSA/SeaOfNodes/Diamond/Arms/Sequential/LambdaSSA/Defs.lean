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

/-- The link block receives the first result as a single parameter.
Destructure it once, then run the unchanged second compiler under a
renaming that places its inputs at the decoded variables. -/
def continuation : Region (Primitive Op) :=
  unpack (dataPorts middle)
    ((Arms.LambdaSSA.lower g.second).renameVars (inputIndex middle.length))

/-- The canonical linked CFG binds the first exit's payload and runs the
second region as its sole local continuation. -/
def lower : Region (Primitive Op) :=
  (Arms.LambdaSSA.lower g.first).linkExits [resultCode middle] (fun _ => continuation g)

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA
