module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Regression

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example (first)

#guard (observe chain).toOption == some ([(1, 0), (2, 1), (5, 2)], [3, 0, 4], none, [none, none, some 5])
#guard (observe varying).toOption == some ([(1, 0)], [3, 0, 2, 4], none, [none, some 13, some 13])
#guard (observe unsaved).toOption == some ([], [0, 1, 2, 3], none, [none, none, some 23])
#guard (match discover (AfterReorder.Second.Example.loop false) first.header with
  | .ok ⟨requests, .initial (.two _ _ _)⟩ => requests == [⟨1, 0⟩, ⟨2, 1⟩]
  | _ => false)

-- Origin 2 survives, but its other operand depends on the latch. Its
-- request uses the correct one-save cut and still fails the actual checker.
#guard (match varying with
  | .ok ⟨_, .initial (.one record)⟩ =>
    record.origins[2]? == some 2 &&
      match Replay.second? record ⟨2, 1⟩ with
      | .error .rejected => true
      | _ => false
  | _ => false)

-- The old two-hoist emitter cannot move the third binding before its
-- second prerequisite is saved. Discovery checks it on the actual seed.
#guard (match Replay.replay Step.Example.loop first.header [⟨1, 0⟩, ⟨5, 1⟩] with
  | .error (.nomination 1 _ .rejected) => true
  | _ => false)

example {plan : Plan _ _ _} (accepted : chain = .ok plan) :
    Step.replayAll Step.Example.loop first.header plan.requests = .ok plan.output :=
  (discover_spec accepted).1

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Regression
