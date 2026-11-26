module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def spec : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 2]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .ne
  limit := 42
  guardRhs := some (.arg 2)
  exitSlot := 2
  exitOrigin := some (.output 1 0)

private def plan : Plan 3 where
  entry := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  copies := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardIndex := 0
  comparison := .ne
  limit := 42
  guardSlot := some 2
  exitSlot := 2
  exitProducer := some 1

private def targets : Checked.Phi.Targets := (lowerBank plan.graph, Generic.lower plan.graph)
private theorem checked : checkPlan 3 spec = some plan := by cbv
private theorem accepted : lowerChecked 3 spec = some targets := by cbv

example : lowerChecked 3 { spec with guardRhs := some (.arg 3) } = none := by cbv
example : lowerChecked 3 { spec with guardRhs := some (.output 1 0) } = none := by cbv

example : plan.guardOperands.addresses = [.output 0 0, .arg 5] := by cbv

example : (bankHeader plan.graph).ops[2]? = some (.binary (.cmp .ne) (.node 2) (.node 0) (.arg 5)) :=
  guard_compare_operand plan

example : (targets.1.block? 0 1).map (·.term) =
    some (.cond (.node 2) 1 [.node 0, .arg 4, .node 1] 2 [.node 1]) := by cbv

-- Inspect the actual emitted CFG. Both branches read from the scheduled
-- header, with the exit arm passing the subtraction's result.
example : match targets.2 with
    | .cfg _ n blocks =>
      if inside : 0 < n then
        match blocks ⟨0, inside⟩ with
        | .let₂ _ (.let₂ _ (.let₂ _ body)) =>
          match body with
          | .let₁ _ (.let₁ _ (.let₁ (.op (.apply .ne) (.pair (.var lhs) (.pair (.var rhs) .unit)))
              (.case (.var predicate) (.br 0 feedback) (.br 1 (.pair (.var result) .unit))))) =>
            (lhs, rhs, predicate, result) = (1, 3, 0, 2) ∧
              feedback = .pair (.var 3) (.pair (.var 7) (.pair (.var 2) .unit))
          | _ => False
        | _ => False
      else False
    | _ => False := by cbv

private def bank (x y z : Word) : WordTuple 3 := .cons x (.cons y (.cons z .nil))
private def input := bank 0 1 5
private def spin := bank 1 0 5
private def mem := Memory.ofList 4 [29, 71, 53, 11]

-- The last activation compares next counter 3 with old slot 2's value 3,
-- even though the subtraction has already produced 2 for that slot.
private theorem nativeReturns :
    plan.graph.ReturnsAfter model input 2 (plan.graph.initial model input) (2 : Word) :=
  .backedge (next := bank 1 1 4) (by cbv)
    (.backedge (next := bank 2 1 3) (by cbv) (.exit (by cbv)))

example : ({ plan with guardSlot := none }).graph.evalBackedges model 2 input = none := by cbv
example : plan.rtlFuel 2 = 14 := rfl
example : ({ plan with guardSlot := none }).rtlFuel 2 = 17 := rfl

example : targets.1.runMain 14 0 (words input) mem = .returned [2] mem :=
  (runMain_fuel_iff plan input mem mem [2] 14).mpr ⟨2, (2 : Word), nativeReturns, by decide, rfl, rfl⟩

example : targets.1.runMain 14 0 (words input) mem = .returned [2] mem := by cbv
example : (targets.1.runMain 13 0 (words input) mem).returnedValues? = none := by cbv
example : targets.1.runMain 6 0 (words (bank 4 1 5)) mem = .returned [4] mem := by cbv

example : Generic.Fuel.run model (inputEnv model input) 3 targets.2 =
    some (0, Generic.packResult model (out := word) (2 : Word)) := by cbv

example : Eval (instruction model) (inputEnv model input) targets.2 mem 0
    (Generic.packResult model (out := word) (2 : Word)) mem :=
  (lambda_return_iff checked accepted _ _ _ _ _).mpr
    ⟨(2 : Word), (plan.graph.returns_iff_mem_denote model _ _).mp ⟨2, nativeReturns⟩, rfl, rfl, rfl⟩

private theorem spinUndefined : plan.program.graph.denote model spin = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact plan.graph.not_returns_of_backedge_invariant model spin value (· = spin) (by cbv)
    (fun old fixed => by
      subst old
      exact ⟨spin, by cbv, rfl⟩)
    ((plan.graph.returns_iff_mem_denote model _ _).mpr present)

example : ∀ returned final, ¬ targets.1.oracle 0 (words spin) mem returned final :=
  (no_finite_return_iff checked accepted _ _).1.mpr spinUndefined

example : ∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin)
    targets.2 mem label payload final :=
  (no_finite_return_iff checked accepted _ _).2.mpr spinUndefined

private def swap : InputPermutation 3 := Equiv.swap 0 1
private def mapped := plan.reindexInputs swap
private def reemitted : Checked.Phi.Targets := (lowerBank mapped.graph, Generic.lower mapped.graph)

example : lowerChecked 3 (spec.reindexInputs swap) = some reemitted := by cbv
example : bankHeader mapped.graph = bankHeader plan.graph := rfl
example : reemitted.1.runMain 14 0 (words (bank 1 0 5)) mem = .returned [2] mem := by cbv
example : Generic.Fuel.run model (inputEnv model (bank 1 0 5)) 3 reemitted.2 =
    some (0, Generic.packResult model (out := word) (2 : Word)) := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
