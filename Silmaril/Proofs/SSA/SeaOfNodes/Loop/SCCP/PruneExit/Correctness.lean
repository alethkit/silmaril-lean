module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Bank.Proofs

open Diamond (Dataflow)
open Diamond.SCCP (TupleCovers)
open RVSDG (extend)
open SeaOfNodes.MLIR (Word sourceInputs)
open SeaOfNodes.MLIR.Lowering (Scope lowerCode)
open Loop.MLIR.CF (TargetOp evalOp model opcode)
open Loop.MLIR.CF.Bank (Label Values bankEnv bankOperands headerScope headerTerm lower)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame Terminator)
open Silmaril.MLIR.Pure (Code)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

private theorem map_lowerCode {ports : List (Diamond.Ty Width)} {past sigs : List (List (Diamond.Ty Width))}
    (feedback : Bool) (flow : Dataflow Loop.MLIR.CF.Op ports past sigs) (scope : Scope ports past Γ)
    (finish : ∀ {Δ}, Scope ports (extend past sigs) Δ → Terminator (Label carried result) [result] Δ) :
    (lowerCode opcode flow scope finish).mapTerm (selectTerm feedback) =
      lowerCode opcode flow scope (fun final => selectTerm feedback (finish final)) := by
  induction flow generalizing Γ with
  | nil => rfl
  | cons op wires rest ih =>
    simp only [lowerCode, Code.mapTerm]
    congr 1
    exact ih _ (fun final => finish final)

variable (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ)
variable (input : Env Γ)

theorem selected_header_shape (feedback : Bool) :
    (selectHeader feedback g).block .header =
      lowerCode opcode g.header (headerScope Γ carried)
        (fun scope =>
          if feedback then .br ⟨.header, bankOperands scope (g.phiInputs .backedge)⟩
          else .br ⟨.exit, .cons (scope.resolveValue g.result) .nil⟩) :=
  by cases feedback <;> exact map_lowerCode _ g.header (headerScope Γ carried) (headerTerm g)

theorem header_shape :
    (directExit g).block .header =
      lowerCode opcode g.header (headerScope Γ carried)
        (fun scope => .br ⟨.exit, .cons (scope.resolveValue g.result) .nil⟩) :=
  selected_header_shape g false

private theorem eval_selectTerm {Δ : List Width} (feedback : Bool)
    (term : Terminator (Label carried result) [result] Δ) (env : Env Δ)
    (frame : Frame (Label carried result)) (selected : isHeader frame.label = feedback)
    (taken : term.eval env = .inl frame) :
    (selectTerm feedback term).eval env = .inl frame := by
  cases term with
  | br => exact taken
  | ret => exact taken
  | condBr test yes no =>
    rcases yes with ⟨trueLabel, yesArgs⟩
    rcases no with ⟨falseLabel, noArgs⟩
    cases trueLabel <;> cases falseLabel
    · exact taken
    · by_cases bit : (env.get test).getLsbD 0 = true
      · simp only [Terminator.eval, ite_eq_left bit] at taken
        obtain rfl := (Sum.inl.inj taken).symm
        have choice : true = feedback := selected
        cases choice
        rfl
      · simp only [Terminator.eval, ite_eq_right bit] at taken
        obtain rfl := (Sum.inl.inj taken).symm
        have choice : false = feedback := selected
        cases choice
        rfl
    · exact taken
    · exact taken

private theorem eval_mapTerm {Δ : List Width} (feedback : Bool)
    (code : Code TargetOp (Terminator (Label carried result) [result]) Δ)
    (env : Env Δ) (frame : Frame (Label carried result)) (selected : isHeader frame.label = feedback)
    (taken : code.eval evalOp (fun term vals => term.eval vals) env = .inl frame) :
    (code.mapTerm (selectTerm feedback)).eval evalOp (fun term vals => term.eval vals) env =
      .inl frame := by
  induction code with
  | terminator term => exact eval_selectTerm feedback term env frame selected taken
  | letOp op operands rest ih => exact ih _ taken

theorem selected_header_frame (feedback : Bool) (old : Values carried)
    (frame : Frame (Label carried result)) (selected : isHeader frame.label = feedback)
    (taken : ((lower g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      .inl frame) :
    ((selectHeader feedback g).block .header).eval evalOp (fun term env => term.eval env)
      ((bankEnv old).append input) = .inl frame :=
  eval_mapTerm feedback _ _ frame selected taken

attribute [local irreducible] solve

theorem rewriteSelected_eq_some_iff (feedback : Bool) {cfg : Cfg TargetOp (Label carried result) Γ [result]} :
    rewriteSelected feedback g facts = some cfg ↔ OnlySuccessor feedback g facts ∧ cfg = selectHeader feedback g := by
  unfold rewriteSelected
  split
  · rename_i admitted
    exact ⟨fun equal => ⟨admitted, (Option.some.inj equal).symm⟩,
      fun equal => congrArg some equal.2.symm⟩
  · rename_i refused
    exact ⟨(fun equal => nomatch equal), fun claims => (refused claims.1).elim⟩

theorem step_exit (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    {old : Values carried} (hold : BankCovers (solve model g facts).2.1 old) :
    ∃ value, g.step model (sourceInputs input) old = .inl value := by
  have step := solve_step model g (input := facts) (entry := sourceInputs input)
    (old := old) covered hold
  cases h : g.step model (sourceInputs input) old with
  | inl value => exact ⟨value, rfl⟩
  | inr next =>
    rw [h] at step
    exact False.elim (admitted.2 step.1)

theorem header_frame (old : Values carried) (value : Word result)
    (taken : g.step model (sourceInputs input) old = .inl value) :
    ((directExit g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      .inl ⟨.exit, .cons value .nil⟩ := by
  apply selected_header_frame g input false old _ rfl
  rw [Loop.MLIR.CF.Bank.lower_header_frame, taken]

private theorem run_at_exit (value : Word result)
    (taken : g.step model (sourceInputs input) (g.initial model (sourceInputs input)) = .inl value) (fuel : Nat) :
    (directExit g).run evalOp fuel input = (lower g).run evalOp fuel input := by
  let old := g.initial model (sourceInputs input)
  have entry := Loop.MLIR.CF.Bank.lower_entry_frame g input
  have header := Loop.MLIR.CF.Bank.lower_header_frame g input old
  change g.step model (sourceInputs input) old = .inl value at taken
  rw [taken] at header
  have direct := header_frame g input old value taken
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have directEntry : (directExit g).entry.eval evalOp (fun term env => term.eval env) input =
        .inl (⟨.header, bankEnv old⟩ : Frame (Label carried result)) := entry
    unfold Cfg.run
    rw [Cfg.runBlock, Cfg.runBlock, directEntry, entry]
    cases fuel with
    | zero => rfl
    | succ fuel =>
      change (directExit g).runBlock evalOp input (fuel + 1) ((directExit g).block .header)
          ((bankEnv old).append input) =
        (lower g).runBlock evalOp input (fuel + 1) ((lower g).block .header) ((bankEnv old).append input)
      rw [Cfg.runBlock, Cfg.runBlock, direct, header]
      cases fuel <;> rfl

theorem run_eq (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    (fuel : Nat) :
    (directExit g).run evalOp fuel input = (lower g).run evalOp fuel input := by
  have initial : BankCovers (solve model g facts).2.1 (g.initial model (sourceInputs input)) :=
    (solve_arrives model g covered .entry).2
  obtain ⟨value, taken⟩ := step_exit g facts input admitted covered initial
  exact run_at_exit g input value taken fuel

theorem denotePart_eq (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input)) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (directExit g)).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) := by
  rw [← Loop.MLIR.CF.Bank.lower_denotePart]
  apply Part.ext
  intro outcome
  simp only [Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff,
    Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run, run_eq g facts input admitted covered]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Bank.Proofs
