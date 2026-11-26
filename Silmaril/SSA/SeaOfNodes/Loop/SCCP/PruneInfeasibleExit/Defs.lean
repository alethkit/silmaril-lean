module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Defs

/-! Drop the infeasible exit occurrence from the emitted carried-bank loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit

open PruneExit (InputFacts)
open Silmaril.MLIR.Arith (Width)

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- The simultaneous SCCP solution marks feedback and leaves exit unmarked. -/
abbrev FeedbackOnly (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :=
  PruneExit.Bank.OnlySuccessor true g facts

/-- Select the existing backedge with its entire typed feedback column. -/
abbrev directFeedback (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) :=
  PruneExit.Bank.selectHeader true g

/-- Emit an unconditional backedge only for a feedback-only solution. -/
abbrev rewrite (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :=
  PruneExit.Bank.rewriteSelected true g facts

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit
