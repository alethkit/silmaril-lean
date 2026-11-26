module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Phi.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Phi.Agreement

/-! # Exact edge and return agreement for the two countdown lowerings -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.FeedbackPlan

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Activation step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom LayoutMatch encodeTuple inputEnv instruction terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {payloads : Nat} (plan : FeedbackPlan payloads)

theorem checked_rtl {entry feedback : List Nat} {result : Nat} {specs : List FeedbackSpec}
    (accepted : checkFeedbackPlan payloads entry feedback result specs = some plan) :
    lowerFeedbackRowChecked payloads entry feedback result specs = some plan.rtl := by
  simp [lowerFeedbackRowChecked, accepted]

theorem ssa_hasType :
    plan.ssa.HasType (inputContext (wordSorts (payloads + 1))) [packed [.value word]] :=
  lower_hasType plan.graph

/-- The chosen predecessor position recovers the actual feedback branch.
Its entire payload is read in one scheduled old environment. -/
theorem feedback_slot_transfer_iff (order : Fin 2 ≃ HeaderIncoming plan.graph)
    (input old : WordTuple (payloads + 1)) {env : Env (Atom model)}
    (matched : LayoutMatch model (headerLayout plan.graph) env (appendTuple old input)
      (plan.graph.header.eval model (appendTuple old input) PUnit.unit))
    (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (extend env .unit)
        (terminatorRegion (slotBranch plan.graph order (order.symm (headerIncoming plan.graph .backedge))))
        start label payload finish ↔
      label = 0 ∧ payload = encodeTuple model (plan.nextBank input old) ∧ finish = start :=
  Phi.Proofs.feedback_slot_transfer_iff plan order input old matched start finish label payload

/-- RTL binds the native next bank at the taken terminator. The emitted
λSSA header executes its producers and transfers that same full tuple. -/
theorem feedback_agrees (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stack : List (Activation Reg)) (mem : Memory) (matchArgs : ArgsMatch fr (appendTuple old input))
    (taken : counter old ≠ 0) :
    let after := headerFrameWithRow plan.updates fr old
    let next := plan.nextBank input old
    step plan.rtl ⟨⟨0, 1, (plan.routes.headerWithRow plan.updates).ops.length⟩, after, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank after next, stack, mem⟩ ∧
    Eval (instruction model) (extend (inputEnv model input) (encodeTuple model old))
      (header plan.graph) mem 0 (encodeTuple model next) mem :=
  Phi.Proofs.feedback_agrees plan input old fr stack mem matchArgs taken

/-- Both finite executions observe the same word and the same entire
final memory. The two source adequacy laws force that memory to be initial. -/
theorem returns_iff (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    plan.rtl.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, returned = [value] ∧
        Eval (instruction model) (inputEnv model input) plan.ssa
          initial 0 (packResult model (out := word) value) final :=
  Phi.Proofs.returns_iff plan input initial final returned

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.FeedbackPlan
