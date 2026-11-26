module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Defs

/-! # One checked countdown plan for machine RTL and explicit-φ λSSA -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

variable {payloads : Nat}

abbrev FeedbackPlan.graph (plan : FeedbackPlan payloads) :=
  plan.routes.graphWithRow plan.updates

abbrev FeedbackPlan.ssa (plan : FeedbackPlan payloads) := lower plan.graph

abbrev FeedbackPlan.phiView (plan : FeedbackPlan payloads) := Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.phiView plan.graph

abbrev FeedbackPlan.nextBank (plan : FeedbackPlan payloads) (input old : WordTuple (payloads + 1)) :=
  plan.routes.nextBankWithRow plan.updates input old

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
