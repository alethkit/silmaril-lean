module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Phi.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Phi.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Activation step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom LayoutMatch encodeTuple encode_injective inputEnv instruction terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {payloads : Nat} (plan : FeedbackPlan payloads)

theorem feedback_slot_transfer_iff (order : Fin 2 ≃ HeaderIncoming plan.graph)
    (input old : WordTuple (payloads + 1)) {env : Env (Atom model)}
    (matched : LayoutMatch model (headerLayout plan.graph) env (appendTuple old input)
      (plan.graph.header.eval model (appendTuple old input) PUnit.unit))
    (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (extend env .unit)
        (terminatorRegion (slotBranch plan.graph order (order.symm (headerIncoming plan.graph .backedge))))
        start label payload finish ↔
      label = 0 ∧ payload = encodeTuple model (plan.nextBank input old) ∧ finish = start := by
  rw [slot_branch_roundtrip]
  change Eval (instruction model) (extend env .unit)
    (.br (edge plan.graph .backedge).target (edge plan.graph .backedge).argument)
    start label payload finish ↔ _
  rw [PhiView.latch_eq_transfer (instruction model) plan.phiView,
    feedback_latch plan.graph model input old matched]
  rfl

theorem feedback_agrees (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stack : List (Activation Reg)) (mem : Memory) (matchArgs : ArgsMatch fr (appendTuple old input))
    (taken : counter old ≠ 0) :
    let after := headerFrameWithRow plan.updates fr old
    let next := plan.nextBank input old
    step plan.rtl ⟨⟨0, 1, (plan.routes.headerWithRow plan.updates).ops.length⟩, after, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank after next, stack, mem⟩ ∧
    Eval (instruction model) (extend (inputEnv model input) (encodeTuple model old))
      (header plan.graph) mem 0 (encodeTuple model next) mem := by
  refine ⟨row_step_feedback plan.routes plan.updates input old fr stack mem matchArgs taken, ?_⟩
  apply (header_backedge_iff plan.graph model input old (plan.nextBank input old) mem mem).mpr
  exact ⟨(row_native_step plan.routes plan.updates input old).trans (ite_eq_right taken), rfl⟩

theorem returns_iff (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    plan.rtl.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, returned = [value] ∧
        Eval (instruction model) (inputEnv model input) plan.ssa
          initial 0 (packResult model (out := word) value) final := by
  rw [FeedbackPlan.rtl, row_returns_iff]
  constructor
  · rintro ⟨value, source, rfl, state⟩
    subst final
    exact ⟨value, rfl, (Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.returns_iff
      plan.graph model input initial value).mp source⟩
  · rintro ⟨value, rfl, typed⟩
    obtain ⟨observed, source, _, same, state⟩ :=
      (lower_eval_iff plan.graph model input initial final 0 (packResult model (out := word) value)).mp typed
    have sameWord : value = observed := encode_injective model (sort := word) (Value.pair.inj same).1
    exact ⟨observed, source, congrArg (fun v => [v]) sameWord, state⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Phi.Proofs
