module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Proofs

open Diamond (Dataflow dataPorts)
open Diamond.SCCP (TupleCovers)
open RVSDG (extend)
open SeaOfNodes.MLIR (Word sourceInputs)
open SeaOfNodes.MLIR.Lowering (Scope lowerCode)
open Loop.MLIR.CF (Label TargetOp evalOp headerScope headerTerm inputSorts lower model opcode)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame Terminator)
open Silmaril.MLIR.Pure (Code)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

private theorem map_lowerCode {ports : List (Diamond.Ty Width)} {past sigs : List (List (Diamond.Ty Width))}
    (flow : Dataflow Loop.MLIR.CF.Op ports past sigs) (scope : Scope ports past Γ)
    (finish : ∀ {Δ}, Scope ports (extend past sigs) Δ → Terminator (Label carried result) [result] Δ) :
    (lowerCode opcode flow scope finish).mapTerm pruneTerm =
      lowerCode opcode flow scope (fun final => pruneTerm (finish final)) := by
  induction flow generalizing Γ with
  | nil => rfl
  | cons op wires rest ih =>
    simp only [lowerCode, Code.mapTerm]
    congr 1
    exact ih _ (fun final => finish final)

variable (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ)
variable (input : Env Γ)

theorem header_shape :
    (directExit g).block .header =
      lowerCode opcode g.header (headerScope Γ carried)
        (fun scope => .br ⟨.exit, .cons (scope.resolveValue g.result) .nil⟩) :=
  map_lowerCode g.header (headerScope Γ carried) (headerTerm g)

private theorem eval_pruneTerm {Δ : List Width} (term : Terminator (Label carried result) [result] Δ)
    (env : Env Δ) (word : Word result) (taken : term.eval env = .inl ⟨.exit, .cons word .nil⟩) :
    (pruneTerm term).eval env = .inl ⟨.exit, .cons word .nil⟩ := by
  cases term with
  | br => exact taken
  | ret => exact taken
  | condBr test yes no =>
    rcases yes with ⟨trueLabel, yesArgs⟩
    rcases no with ⟨falseLabel, noArgs⟩
    cases trueLabel <;> cases falseLabel
    · exact taken
    · by_cases h : (env.get test).getLsbD 0 = true
      · simp only [Terminator.eval, ite_eq_left h] at taken
        cases taken
      · simp only [Terminator.eval, ite_eq_right h] at taken
        exact taken
    · exact taken
    · exact taken

private theorem eval_mapTerm {Δ : List Width}
    (code : Code TargetOp (Terminator (Label carried result) [result]) Δ)
    (env : Env Δ) (word : Word result)
    (taken : code.eval evalOp (fun term vals => term.eval vals) env = .inl ⟨.exit, .cons word .nil⟩) :
    (code.mapTerm pruneTerm).eval evalOp (fun term vals => term.eval vals) env =
      .inl ⟨.exit, .cons word .nil⟩ := by
  induction code with
  | terminator term => exact eval_pruneTerm term env word taken
  | letOp op operands rest ih => exact ih _ taken

attribute [local irreducible] solve

theorem rewrite_eq_some_iff {cfg : Cfg TargetOp (Label carried result) Γ [result]} :
    rewrite g facts = some cfg ↔ ExitOnly g facts ∧ cfg = directExit g := by
  unfold rewrite
  split
  · rename_i admitted
    exact ⟨fun equal => ⟨admitted, (Option.some.inj equal).symm⟩,
      fun equal => congrArg some equal.2.symm⟩
  · rename_i refused
    exact ⟨(fun equal => nomatch equal), fun claims => (refused claims.1).elim⟩

theorem step_exit (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    {old : Word carried} (hold : BankCovers (solve model g facts).2.1 (.cons old .nil)) :
    ∃ value, g.step model (sourceInputs input) (.cons old .nil) = .inl value := by
  have step := solve_step model g (input := facts) (entry := sourceInputs input)
    (old := .cons old .nil) covered hold
  cases h : g.step model (sourceInputs input) (.cons old .nil) with
  | inl value => exact ⟨value, rfl⟩
  | inr next =>
    rw [h] at step
    exact False.elim (admitted.2 step.1)

theorem header_frame (old : Word carried) (value : Word result)
    (taken : g.step model (sourceInputs input) (.cons old .nil) = .inl value) :
    ((directExit g).block .header).eval evalOp (fun term env => term.eval env) (.cons old input) =
      .inl ⟨.exit, .cons value .nil⟩ := by
  apply eval_mapTerm
  rw [Loop.MLIR.CF.lower_header_frame, taken]

private theorem run_at_exit (old : Word carried) (value : Word result)
    (initial : (g.initial model (sourceInputs input)).get .head = old)
    (taken : g.step model (sourceInputs input) (.cons old .nil) = .inl value) (fuel : Nat) :
    (directExit g).run evalOp fuel input = (lower g).run evalOp fuel input := by
  have entry := Loop.MLIR.CF.lower_entry_frame g input
  rw [initial] at entry
  have header := Loop.MLIR.CF.lower_header_frame g input old
  rw [taken] at header
  have direct := header_frame g input old value taken
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have directEntry : (directExit g).entry.eval evalOp (fun term env => term.eval env) input =
        .inl (⟨.header, .cons old .nil⟩ : Frame (Label carried result)) := entry
    unfold Cfg.run
    rw [Cfg.runBlock, Cfg.runBlock, directEntry, entry]
    cases fuel with
    | zero => rfl
    | succ fuel =>
      change (directExit g).runBlock evalOp input (fuel + 1) ((directExit g).block .header) (.cons old input) =
        (lower g).runBlock evalOp input (fuel + 1) ((lower g).block .header) (.cons old input)
      rw [Cfg.runBlock, Cfg.runBlock, direct, header]
      cases fuel <;> rfl

theorem run_eq (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    (fuel : Nat) :
    (directExit g).run evalOp fuel input = (lower g).run evalOp fuel input := by
  have initial : BankCovers (solve model g facts).2.1 (g.initial model (sourceInputs input)) :=
    (solve_arrives model g covered .entry).2
  generalize h : g.initial model (sourceInputs input) = latch at initial ⊢
  cases latch with
  | cons old tail =>
    cases tail
    obtain ⟨value, taken⟩ := step_exit g facts input admitted covered initial
    exact run_at_exit g input old value (congrArg (fun bank => bank.get .head) h) taken fuel

theorem denotePart_eq (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input)) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (directExit g)).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) := by
  rw [← Loop.MLIR.CF.lower_denotePart]
  apply Part.ext
  intro outcome
  simp only [Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff,
    Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run, run_eq g facts input admitted covered]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Proofs
