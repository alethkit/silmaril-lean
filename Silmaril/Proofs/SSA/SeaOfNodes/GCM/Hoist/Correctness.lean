module

public import Silmaril.SSA.SeaOfNodes.GCM.Hoist.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Silmaril.MLIR.Pure (Eval OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Hoist

variable {Op : OpSignature} {Input : List Width} {arg out : Width}
variable {g : Diamond Op Input arg out} {tree : DominatorTree g.before}
variable {cut : Point (Label arg out false)}
variable {emitted : Cfg Op (Label arg out true) Input [out, out]}

theorem hoistAt?_eq_some_iff :
    g.hoistAt? tree cut = some emitted ↔
      cut = entryCut ∧ checkPlacement tree operandSites useSites entryCut = true ∧ emitted = g.after := by
  rcases cut with ⟨block, index⟩
  cases block with
  | some label => simp [Diamond.hoistAt?, entryCut]
  | none =>
    by_cases atEntry : index = 1
    · subst index
      simp [Diamond.hoistAt?, entryCut]
      intro _
      exact eq_comm
    · simp [Diamond.hoistAt?, entryCut, atEntry]

theorem hoistAt?_legal (changed : g.hoistAt? tree cut = some emitted) :
    Legal g.before operandSites useSites cut := by
  obtain ⟨rfl, checked, _⟩ := hoistAt?_eq_some_iff.mp changed
  exact checkPlacement_sound tree checked

section Execution

variable (g : Diamond Op Input arg out) (evalOp : Eval Op) (input : Env Input)

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
  ⟨rfl, rfl⟩

theorem throughArm_eq_join :
    throughArm g.before evalOp input = .inl ⟨.join, g.joinArgs evalOp input⟩ ∧
    throughArm g.after evalOp input = .inl ⟨.join, g.joinArgs evalOp input⟩ := by
  obtain ⟨beforeRoute, afterRoute⟩ := entry_eval_routes g evalOp input
  constructor
  · unfold throughArm Diamond.joinArgs
    rw [beforeRoute]
    cases (input.get g.selector).getLsbD 0 <;> rfl
  · unfold throughArm Diamond.joinArgs
    rw [afterRoute]
    cases (input.get g.selector).getLsbD 0 <;> rfl

private theorem run_throughArm {hoisted : Bool}
    (cfg : Cfg Op (Label arg out hoisted) Input [out, out]) (fuel : Nat) :
    cfg.run evalOp (fuel + 2) input =
      match throughArm cfg evalOp input with
      | .inl join => cfg.runFrom evalOp fuel input join
      | .inr result => some result := by
  unfold Cfg.run throughArm
  rw [Cfg.runBlock]
  cases start : cfg.entry.eval evalOp (fun term env => term.eval env) input with
  | inr result => rfl
  | inl arm =>
    change cfg.runBlock evalOp input (fuel + 1) (cfg.block arm.label) (arm.args.append input) = _
    rw [Cfg.runBlock]
    change _ = (match (cfg.block arm.label).eval evalOp (fun term env => term.eval env)
        (arm.args.append input) with
      | .inl next => cfg.runFrom evalOp fuel input next
      | .inr result => some result)
    cases (cfg.block arm.label).eval evalOp (fun term env => term.eval env) (arm.args.append input) <;> rfl

theorem run_observation (fuel : Nat) :
    let expected := if 3 ≤ fuel then some (g.joinArgs evalOp input) else none
    g.before.run evalOp fuel input = expected ∧ g.after.run evalOp fuel input = expected := by
  rcases fuel with _ | fuel
  · exact ⟨rfl, rfl⟩
  rcases fuel with _ | fuel
  · obtain ⟨beforeRoute, afterRoute⟩ := entry_eval_routes g evalOp input
    constructor
    · unfold Cfg.run
      rw [Cfg.runBlock, beforeRoute]
      rfl
    · unfold Cfg.run
      rw [Cfg.runBlock, afterRoute]
      rfl
  · obtain ⟨beforeJoin, afterJoin⟩ := throughArm_eq_join g evalOp input
    constructor <;> (first | rw [run_throughArm, beforeJoin] | rw [run_throughArm, afterJoin])
    all_goals
      cases fuel with
      | zero => rfl
      | succ fuel =>
        rw [ite_eq_left (by omega)]
        cases g.joinArgs evalOp input with
        | cons _ args =>
          cases args with
          | cons _ tail =>
            cases tail
            rfl

end Execution

theorem hoistAt?_run_eq (changed : g.hoistAt? tree cut = some emitted)
    (evalOp : Eval Op) (fuel : Nat) (input : Env Input) :
    g.before.run evalOp fuel input = emitted.run evalOp fuel input := by
  obtain ⟨_, _, rfl⟩ := hoistAt?_eq_some_iff.mp changed
  obtain ⟨beforeRun, afterRun⟩ := run_observation g evalOp input fuel
  exact beforeRun.trans afterRun.symm

theorem pickAndHoist?_correct (picked : g.pickAndHoist? tree = some (cut, emitted)) :
    cut ∈ candidateCuts g.before blocks ∧ Legal g.before operandSites useSites cut ∧
      ∀ (evalOp : Eval Op) (fuel : Nat) (input : Env Input),
        g.before.run evalOp fuel input = emitted.run evalOp fuel input := by
  unfold Diamond.pickAndHoist? at picked
  change (discoverPlacement tree blocks operandSites useSites >>= _) = _ at picked
  obtain ⟨chosen, found, rewritten⟩ := Option.bind_eq_some_iff.mp picked
  change (g.hoistAt? tree chosen >>= _) = _ at rewritten
  obtain ⟨cfg, changed, paired⟩ := Option.bind_eq_some_iff.mp rewritten
  cases paired
  exact ⟨(discoverPlacement_sound tree blocks found).1,
    hoistAt?_legal changed, hoistAt?_run_eq changed⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist
