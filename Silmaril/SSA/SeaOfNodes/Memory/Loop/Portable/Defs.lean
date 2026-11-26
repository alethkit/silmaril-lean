module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs

/-! # A shared finite observation of a native memory loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable

open Memory.Diamond.LambdaSSA (Instruction inputEnv packet wordPacket)
open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {args : List ValueSort} {cells : Nat}

/-- All backends observe the same source word and entire final heap.
The count is the number of backedges, so the first successful numbered
bound includes one additional activation. -/
structure Observation (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (backedges : Nat) (word : Word) (final : Heap cells) : Prop where
  lambdaTyped : (LambdaSSA.lower graph).HasType (LambdaSSA.inputContext args) [wordPacket]
  lambdaReturn : Eval (Instruction cells) (inputEnv input) (LambdaSSA.lower graph)
    initial 0 (packet word) final
  lambdaCounted : LambdaSSA.FollowAfter graph input backedges initial word final
  thetaBefore : graph.lowerTheta.run (thetaRuntime cells) backedges (encodeInput initial input) = none
  thetaAt : graph.lowerTheta.run (thetaRuntime cells) (backedges + 1) (encodeInput initial input) =
    some (encodeResult word final)
  petriCompletion : Finishes (thetaRuntime cells) graph.lowerTheta
    (encodeInput initial input) (encodeResult word final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable
