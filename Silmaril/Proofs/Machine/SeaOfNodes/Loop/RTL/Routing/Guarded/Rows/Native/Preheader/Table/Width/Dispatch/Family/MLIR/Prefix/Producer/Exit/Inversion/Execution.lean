module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame Opcode packValues)
open Silmaril.Machine.RTL.SSA (StepsNWithin toLambdaSSA)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp TargetOp)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
variable {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
variable {origins : List (HeaderWord new old sigs)}

private theorem return_after_transfers {live : Nat}
    {cfg : Cfg TargetOp (Label live old tests) (wordsTy new) [i64]}
    {input : Silmaril.MLIR.Arith.Env (wordsTy new)} {start finish count}
    (path : Transfers cfg input count start finish)
    {fuel : Nat} {result : Silmaril.MLIR.Arith.Env [i64]}
    (observed : cfg.runFrom evalOp fuel input start = some result) :
    ∃ remaining, fuel = count + remaining ∧ cfg.runFrom evalOp remaining input finish = some result := by
  induction path generalizing fuel with
  | refl _ => exact ⟨fuel, (Nat.zero_add fuel).symm, observed⟩
  | next step _ ih =>
    cases fuel with
    | zero => cases observed
    | succ fuel =>
      unfold Cfg.runFrom at observed
      rw [Cfg.runBlock, step] at observed
      obtain ⟨remaining, spent, ran⟩ := ih observed
      exact ⟨remaining, by omega, ran⟩

private theorem invert_exit {compiled : Compiled mapping source origins} {input : WordTuple new}
    {mem : Memory} {carried : WordTuple old} {before : Frame Reg} {expected value : Word}
    (exit : Taken compiled input mem carried before expected) (fuel : Nat)
    (observed : compiled.setup.cf.runFrom evalOp fuel (wordEnv input) (headerFrame _ _ carried) =
      some (.cons value .nil)) :
    expected = value ∧ 2 ≤ fuel := by
  cases fuel with
  | zero => cases observed
  | succ fuel =>
    unfold Cfg.runFrom at observed
    rw [Cfg.runBlock, exit.cfBranch] at observed
    cases fuel with
    | zero => cases observed
    | succ fuel =>
      change compiled.setup.cf.runBlock evalOp (wordEnv input) (fuel + 1) (compiled.setup.cf.block .exit)
        ((Silmaril.MLIR.Arith.Env.cons (w := i64) expected .nil).append (wordEnv input)) =
        some (.cons value .nil) at observed
      rw [Cfg.runBlock, exit.cfReturn] at observed
      cases observed
      exact ⟨rfl, by omega⟩

theorem from_header (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word) (carried : WordTuple old) (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input))
    (observed : compiled.setup.cf.runFrom evalOp fuel (wordEnv input) (headerFrame _ _ carried) =
      some (.cons value .nil)) :
    ∃ slots finish after,
      source.ReturnsAlong (mapping.pull input) slots carried value ∧
      Realized compiled.setup input mem slots carried before finish after ∧
      Taken compiled input mem finish after value ∧ cfCost slots + 2 ≤ fuel := by
  induction fuel using Nat.strongRecOn generalizing carried before with
  | ind fuel ih =>
    cases step : source.step (mapping.pull input) carried with
    | inl expected =>
      have exit := Exit.taken compiled input mem carried before expected matched step
      obtain ⟨rfl, bound⟩ := invert_exit exit fuel observed
      exact ⟨[], carried, before, .exit step, .stop matched, exit, bound⟩
    | inr pair =>
      obtain ⟨slot, next⟩ := pair
      obtain ⟨middle, visit⟩ :=
        Prefix.visit_correct compiled.setup input mem before matched (header_match compiled input carried) step
      obtain ⟨remaining, spent, ran⟩ := return_after_transfers visit.cfPath observed
      obtain ⟨_, _, cut, _, _⟩ := visit.cut
      obtain ⟨slots, finish, after, sourcePath, path, exit, bound⟩ :=
        ih remaining (by omega) next middle cut.rebound ran
      refine ⟨slot :: slots, finish, after, .feedback step sourcePath, .visit visit path, exit, ?_⟩
      simp only [cfCost, List.map_cons, List.sum_cons] at bound ⊢
      omega

theorem from_entry (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word)
    (observed : compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :
    let initial := source.primary.initial model (mapping.pull input)
    ∃ slots finish before after,
      compiled.rtl.start 0 (words input) mem =
        some ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩ ∧
      StepsNWithin compiled.rtl [] (entrySigs.length + 1)
        ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩ ⟨⟨0, 1, 0⟩, before, [], mem⟩ ∧
      source.ReturnsAlong (mapping.pull input) slots initial value ∧
      Realized compiled.setup input mem slots initial before finish after ∧
      Taken compiled input mem finish after value ∧ cfCost slots + 2 + 1 ≤ fuel := by
  cases fuel with
  | zero => cases observed
  | succ fuel =>
    unfold Cfg.run at observed
    rw [Cfg.runBlock, Producer.entry_frame compiled input] at observed
    obtain ⟨started, before, entered, matched⟩ := Family.entry_packet mapping source compiled.accepted input mem
    obtain ⟨slots, finish, after, path, feedback, exit, bound⟩ :=
      from_header compiled input mem fuel value _ before matched observed
    exact ⟨slots, finish, before, after, started, entered, path, feedback, exit, Nat.succ_le_succ bound⟩

theorem reflect (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word)
    (observed : compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil))
    (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    ∃ slots, source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value ∧
      cfCost slots + 2 + 1 ≤ fuel ∧
      compiled.rtl.runMain (entrySigs.length + 1 + (rtlCost sigs.length slots + (sigs.length + 2)))
        0 (words input) mem = .returned [value] mem ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) ∧
      Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
        (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 (packValues [value]) mem := by
  obtain ⟨slots, _, _, _, _, _, path, _, _, bound⟩ := from_entry compiled input mem fuel value observed
  obtain ⟨rtl, cf, region⟩ := Exit.returns compiled input mem path env entry
  exact ⟨slots, path, bound, rtl, cf, region⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Proofs
