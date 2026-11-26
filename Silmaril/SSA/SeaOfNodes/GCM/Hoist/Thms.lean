module

public import Silmaril.SSA.SeaOfNodes.GCM.Hoist.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.Correctness

/-! # Legal cuts and observations for the typed diamond hoist -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Hoist

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Input : List Width} {arg out : Width}
variable {g : Diamond Op Input arg out} {tree : DominatorTree g.before}
variable {cut : Point (Label arg out false)}
variable {emitted : Cfg Op (Label arg out true) Input [out, out]}

/-- The emitter accepts the supported cut exactly when the checker accepts it. -/
theorem hoistAt?_eq_some_iff :
    g.hoistAt? tree cut = some emitted ↔
      cut = entryCut ∧ checkPlacement tree operandSites useSites entryCut = true ∧ emitted = g.after :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.hoistAt?_eq_some_iff

/-- An emitted CFG comes from a cut with available operands and dominated uses. -/
theorem hoistAt?_legal (changed : g.hoistAt? tree cut = some emitted) :
    Legal g.before operandSites useSites cut :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.hoistAt?_legal changed

section Execution

variable (g : Diamond Op Input arg out) (evalOp : Eval Op) (input : Env Input)

/-- The same condition selects the same arm. Both original edge arguments
are kept in order and the true edge carries one extra result argument. -/
theorem entry_eval_routes :
    g.before.entry.eval evalOp (fun term env => term.eval env) input =
      .inl (if (input.get g.selector).getLsbD 0 then
        ⟨.left, .cons (g.seedValue evalOp input) (.cons (input.get g.leftExtra) .nil)⟩
      else ⟨.right, .cons (input.get g.fallback) (.cons (input.get g.rightExtra) .nil)⟩) ∧
    g.after.entry.eval evalOp (fun term env => term.eval env) input =
      .inl (if (input.get g.selector).getLsbD 0 then
        ⟨.left, .cons (g.seedValue evalOp input) (.cons (input.get g.leftExtra)
          (.cons (g.resultValue evalOp input) .nil))⟩
      else ⟨.right, .cons (input.get g.fallback) (.cons (input.get g.rightExtra) .nil)⟩) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.entry_eval_routes g evalOp input

/-- Each branch delivers the same ordered arguments to the join on both CFGs. -/
theorem throughArm_eq_join :
    throughArm g.before evalOp input = .inl ⟨.join, g.joinArgs evalOp input⟩ ∧
    throughArm g.after evalOp input = .inl ⟨.join, g.joinArgs evalOp input⟩ :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.throughArm_eq_join g evalOp input

/-- Exactly three block executions are needed to return the ordered join
arguments. This observation holds for every pure total operation model. -/
theorem run_observation (fuel : Nat) :
    let expected := if 3 ≤ fuel then some (g.joinArgs evalOp input) else none
    g.before.run evalOp fuel input = expected ∧ g.after.run evalOp fuel input = expected :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.run_observation g evalOp input fuel

end Execution

/-- A successful checked rewrite preserves the observation at every fuel budget. -/
theorem hoistAt?_run_eq (changed : g.hoistAt? tree cut = some emitted)
    (evalOp : Eval Op) (fuel : Nat) (input : Env Input) :
    g.before.run evalOp fuel input = emitted.run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.hoistAt?_run_eq changed evalOp fuel input

/-- The pass returns an enumerated legal cut and a typed CFG with the same
finite execution observations for all inputs and all fuel budgets. -/
theorem pickAndHoist?_correct (picked : g.pickAndHoist? tree = some (cut, emitted)) :
    cut ∈ candidateCuts g.before blocks ∧ Legal g.before operandSites useSites cut ∧
      ∀ (evalOp : Eval Op) (fuel : Nat) (input : Env Input),
        g.before.run evalOp fuel input = emitted.run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.pickAndHoist?_correct picked

/-- The result of a finite execution is preserved and reflected. -/
theorem pickAndHoist?_returns_iff (picked : g.pickAndHoist? tree = some (cut, emitted))
    (evalOp : Eval Op) (input : Env Input) (result : Env [out, out]) :
    (∃ fuel, g.before.run evalOp fuel input = some result) ↔
      ∃ fuel, emitted.run evalOp fuel input = some result :=
  exists_congr (fun fuel => by rw [(pickAndHoist?_correct picked).2.2 evalOp fuel input])

end Silmaril.SSA.SeaOfNodes.GCM.Hoist
