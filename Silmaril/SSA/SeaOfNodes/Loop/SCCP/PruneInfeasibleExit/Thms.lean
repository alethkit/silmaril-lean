module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Correctness

/-! A feedback-only SCCP certificate preserves the exact emitted backedge
frame and excludes finite returns on every covered input. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit

open Diamond.SCCP (TupleCovers)
open PruneExit (InputFacts)
open SeaOfNodes.MLIR (sourceInputs)
open SeaOfNodes.MLIR.Lowering (lowerCode)
open Loop.MLIR.CF (TargetOp evalOp model opcode)
open Loop.MLIR.CF.Bank (Label Values bankEnv bankOperands headerScope lower lower_header_frame)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs} {facts : InputFacts Γ}
variable {input : Env Γ} {cfg : Cfg TargetOp (Label carried result) Γ [result]}

theorem rewrite_eq_some_iff : rewrite g facts = some cfg ↔ FeedbackOnly g facts ∧ cfg = directFeedback g :=
  PruneExit.Bank.rewriteSelected_eq_some_iff true

/-- An unmarked backedge or a marked exit prevents specialization. -/
theorem rewrite_eq_none_iff : rewrite g facts = none ↔ ¬ FeedbackOnly g facts :=
  PruneExit.Bank.rewriteSelected_eq_none_iff true

theorem entry_eq (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) :
    (directFeedback g).entry = (lower g).entry := rfl

theorem exit_eq (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) :
    (directFeedback g).block .exit = (lower g).block .exit := rfl

/-- The header bindings end in one branch carrying the original feedback
column in order. The operand reads all use the current activation's scope. -/
theorem header_shape (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) :
    (directFeedback g).block .header =
      lowerCode opcode g.header (headerScope Γ carried)
        (fun scope => .br ⟨.header, bankOperands scope (g.phiInputs .backedge)⟩) :=
  PruneExit.Bank.selected_header_shape true g

attribute [local irreducible] solve

theorem step_feedback (admitted : FeedbackOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    {old : Values carried} (hold : BankCovers (solve model g facts).2.1 old) :
    ∃ next, g.step model (sourceInputs input) old = .inr next :=
  Proofs.step_feedback admitted covered hold

/-- A native backedge step supplies exactly the same latch to the direct branch. -/
theorem header_frame {old next : Values carried}
    (taken : g.step model (sourceInputs input) old = .inr next) :
    ((directFeedback g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      .inl ⟨.header, bankEnv next⟩ :=
  Proofs.header_frame taken

/-- Both CFGs choose the same successor and payload at every covered arrival. -/
theorem arrives_frame (admitted : FeedbackOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    {via : Incoming} {count : Nat} {old : Values carried}
    (arrived : Arrives model g (sourceInputs input) via count old) :
    ((directFeedback g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      ((lower g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) := by
  have reached := solve_arrives model g (input := facts) covered arrived
  obtain ⟨next, taken⟩ := step_feedback admitted covered reached.2
  rw [header_frame taken, lower_header_frame, taken]

/-- No finite native return is possible under a feedback-only solution. -/
theorem no_finite_return (admitted : FeedbackOnly g facts) (covered : TupleCovers facts (sourceInputs input)) :
    ¬ ∃ value, g.Returns model (sourceInputs input) value :=
  fun ⟨_, returned⟩ => admitted.2 (solve_returns model g (input := facts) covered returned).1

/-- For a successful rewrite both CFGs exhaust every finite block budget. -/
theorem runs_none (rewritten : rewrite g facts = some cfg) (covered : TupleCovers facts (sourceInputs input))
    (fuel : Nat) : cfg.run evalOp fuel input = none ∧ (lower g).run evalOp fuel input = none :=
  let ⟨admitted, same⟩ := rewrite_eq_some_iff.mp rewritten
  same ▸ Proofs.runs_none admitted covered fuel

theorem run_eq (rewritten : rewrite g facts = some cfg) (covered : TupleCovers facts (sourceInputs input))
    (fuel : Nat) : cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  let both := runs_none rewritten covered fuel
  both.1.trans both.2.symm

theorem denotePart_eq_none (rewritten : rewrite g facts = some cfg)
    (covered : TupleCovers facts (sourceInputs input)) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input = Part.none :=
  let ⟨admitted, same⟩ := rewrite_eq_some_iff.mp rewritten
  same ▸ Proofs.denotePart_eq_none admitted covered

/-- The target partial observation agrees with the native partial return. -/
theorem denotePart_eq (rewritten : rewrite g facts = some cfg) (covered : TupleCovers facts (sourceInputs input)) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) :=
  let ⟨admitted, same⟩ := rewrite_eq_some_iff.mp rewritten
  same ▸ Proofs.denotePart_eq admitted covered

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit
