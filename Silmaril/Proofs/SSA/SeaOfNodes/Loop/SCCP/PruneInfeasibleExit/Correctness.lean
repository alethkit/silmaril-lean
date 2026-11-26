module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Proofs

open Diamond.SCCP (TupleCovers)
open PruneExit (InputFacts)
open SeaOfNodes.MLIR (Word sourceInputs)
open Loop.MLIR.CF (evalOp model)
open Loop.MLIR.CF.Bank (Label Values bankEnv lower lower_entry_frame lower_header_frame lower_denotePart)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs} {facts : InputFacts Γ}
variable {input : Env Γ}

attribute [local irreducible] solve

theorem step_feedback (admitted : FeedbackOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    {old : Values carried} (hold : BankCovers (solve model g facts).2.1 old) :
    ∃ next, g.step model (sourceInputs input) old = .inr next := by
  have step := solve_step model g (input := facts) (entry := sourceInputs input) (old := old) covered hold
  cases taken : g.step model (sourceInputs input) old with
  | inl value =>
    rw [taken] at step
    exact (admitted.2 step.1).elim
  | inr next => exact ⟨next, rfl⟩

theorem header_frame {old next : Values carried}
    (taken : g.step model (sourceInputs input) old = .inr next) :
    ((directFeedback g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      .inl ⟨.header, bankEnv next⟩ := by
  apply PruneExit.Bank.selected_header_frame (g := g) (input := input) true old _ rfl
  rw [lower_header_frame, taken]

private theorem runFrom_none (admitted : FeedbackOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    (fuel : Nat) {via : Incoming} {count : Nat} {old : Values carried}
    (arrived : Arrives model g (sourceInputs input) via count old) :
    (directFeedback g).runFrom evalOp fuel input ⟨.header, bankEnv old⟩ = none ∧
      (lower g).runFrom evalOp fuel input ⟨.header, bankEnv old⟩ = none := by
  induction fuel generalizing via count old with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    have reached := solve_arrives model g (input := facts) covered arrived
    obtain ⟨next, taken⟩ := step_feedback admitted covered reached.2
    have original := lower_header_frame g input old
    rw [taken] at original
    have pruned := header_frame (g := g) (input := input) taken
    have rest := ih (.backedge arrived taken)
    constructor
    · unfold Cfg.runFrom
      rw [Cfg.runBlock, pruned]
      exact rest.1
    · unfold Cfg.runFrom
      rw [Cfg.runBlock, original]
      exact rest.2

theorem runs_none (admitted : FeedbackOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    (fuel : Nat) :
    (directFeedback g).run evalOp fuel input = none ∧ (lower g).run evalOp fuel input = none := by
  cases fuel with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel =>
    have entry := lower_entry_frame g input
    have prunedEntry : (directFeedback g).entry.eval evalOp (fun term env => term.eval env) input =
        .inl (⟨.header, bankEnv (g.initial model (sourceInputs input))⟩ : Frame (Label carried result)) := entry
    have rest := runFrom_none admitted covered fuel .entry
    constructor
    · unfold Cfg.run
      rw [Cfg.runBlock, prunedEntry]
      exact rest.1
    · unfold Cfg.run
      rw [Cfg.runBlock, entry]
      exact rest.2

theorem denotePart_eq (admitted : FeedbackOnly g facts) (covered : TupleCovers facts (sourceInputs input)) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (directFeedback g)).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) := by
  rw [← lower_denotePart]
  apply Part.ext
  intro outcome
  simp only [Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff, Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run,
    fun fuel => (runs_none admitted covered fuel).1, fun fuel => (runs_none admitted covered fuel).2]

theorem denotePart_eq_none (admitted : FeedbackOnly g facts) (covered : TupleCovers facts (sourceInputs input)) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (directFeedback g)).denotePart evalOp input = Part.none :=
  (Silmaril.MLIR.CF.SwitchAssert.Cfg.denotePart_eq_none_iff _ _ _).mpr
    ((Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_diverges_iff _ _ _).mpr (fun fuel => (runs_none admitted covered fuel).1))

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Proofs
