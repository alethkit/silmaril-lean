module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Correctness

/-! Soundness and routing of constant-exit pruning in the typed MLIR CFG. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit

open Diamond.SCCP (TupleCovers)
open SeaOfNodes.MLIR (Word sourceInputs)
open SeaOfNodes.MLIR.Lowering (lowerCode)
open Loop.MLIR.CF (Label TargetOp evalOp headerScope lower model opcode)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs} {facts : InputFacts Γ}
variable {input : Env Γ} {cfg : Cfg TargetOp (Label carried result) Γ [result]}

attribute [local irreducible] solve

theorem rewrite_eq_some_iff : rewrite g facts = some cfg ↔ ExitOnly g facts ∧ cfg = directExit g :=
  Proofs.rewrite_eq_some_iff g facts

/-- The preheader retains its original branch and entry Φ operand. -/
theorem entry_eq (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) :
    (directExit g).entry = (lower g).entry := rfl

/-- The retained exit block still returns its sole block argument. -/
theorem exit_eq (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) :
    (directExit g).block .exit = (lower g).block .exit := rfl

/-- The unchanged header bindings now end in a single edge to the original
exit label. Its operand is the original source result wire. -/
theorem header_shape (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) :
    (directExit g).block .header =
      lowerCode opcode g.header (headerScope Γ carried)
        (fun scope => .br ⟨.exit, .cons (scope.resolveValue g.result) .nil⟩) :=
  Proofs.header_shape g

/-- A covered native execution cannot arrive through the removed occurrence. -/
theorem no_backedge_arrival (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    {count : Nat} {old} (arrived : Arrives model g (sourceInputs input) .backedge count old) : False :=
  admitted.2 (solve_arrives model g (input := facts) covered arrived).1

/-- At a covered latch, the native step exits and supplies its exact readback. -/
theorem step_exit (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    {old : Word carried} (hold : BankCovers (solve model g facts).2.1 (.cons old .nil)) :
    ∃ value, g.step model (sourceInputs input) (.cons old .nil) = .inl value :=
  Proofs.step_exit g facts input admitted covered hold

/-- The direct edge routes the exact native exit argument. The target block
executes with this argument followed by the same captured input environment. -/
theorem header_frame (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs)
    (input : Env Γ) (old : Word carried) (value : Word result)
    (taken : g.step model (sourceInputs input) (.cons old .nil) = .inl value) :
    ((directExit g).block .header).eval evalOp (fun term env => term.eval env) (.cons old input) =
      .inl ⟨.exit, .cons value .nil⟩ :=
  Proofs.header_frame g input old value taken

/-- The original and pruned CFGs agree on successor state at each covered header arrival. -/
theorem arrives_frame (admitted : ExitOnly g facts) (covered : TupleCovers facts (sourceInputs input))
    {via : Incoming} {count : Nat} {old : Word carried}
    (arrived : Arrives model g (sourceInputs input) via count (.cons old .nil)) :
    ((directExit g).block .header).eval evalOp (fun term env => term.eval env) (.cons old input) =
      ((lower g).block .header).eval evalOp (fun term env => term.eval env) (.cons old input) := by
  have latch := (solve_arrives model g (input := facts) covered arrived)
  obtain ⟨value, taken⟩ := step_exit admitted covered latch.2
  rw [header_frame g input old value taken, Loop.MLIR.CF.lower_header_frame, taken]

/-- Pruning preserves the actual CFG observation at every block budget. -/
theorem run_eq (rewritten : rewrite g facts = some cfg)
    (covered : TupleCovers facts (sourceInputs input)) (fuel : Nat) :
    cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  let ⟨admitted, same⟩ := rewrite_eq_some_iff.mp rewritten
  same ▸ Proofs.run_eq g facts input admitted covered fuel

/-- The successful rewrite has the same partial observation as native
evaluation, including the exact singleton result environment. -/
theorem denotePart_eq (rewritten : rewrite g facts = some cfg)
    (covered : TupleCovers facts (sourceInputs input)) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) :=
  let ⟨admitted, same⟩ := rewrite_eq_some_iff.mp rewritten
  same ▸ Proofs.denotePart_eq g facts input admitted covered

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit
