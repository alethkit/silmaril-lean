module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Thms

/-! Delete the infeasible backedge from the emitted one-word MLIR loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit

open Diamond (Val dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)
open SeaOfNodes.MLIR (Word)
open Loop.MLIR.CF (Label TargetOp lower model inputSorts)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Terminator)

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

instance wordBankEq (w : Width) : BankDecidableEq model.value (dataPorts [.data w]) where
  atPort i := Fin.cases (motive := fun j =>
    DecidableEq (Val model.value (dataPorts [.data w])[j]))
    (inferInstance : DecidableEq (Word w)) (fun j => j.elim0) i

abbrev InputFacts (Γ : List Width) :=
  Tuple (Fact model.value) (dataPorts (inputSorts Γ))

/-- Require a marked exit and an unmarked backedge at the simultaneous fixed point. -/
def ExitOnly (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) : Prop :=
  let edges := (solve model g facts).1
  exitIndex ∈ edges ∧ incomingIndex .backedge ∉ edges

instance (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :
    Decidable (ExitOnly g facts) :=
  inferInstanceAs (Decidable (exitIndex ∈ (solve model g facts).1 ∧
    incomingIndex .backedge ∉ (solve model g facts).1))

/-- Specialize the header conditional using its exact false edge and operands. -/
def pruneTerm {Δ : List Width} : Terminator (Label carried result) [result] Δ →
    Terminator (Label carried result) [result] Δ
  | .condBr _ ⟨.header, _⟩ ⟨.exit, args⟩ => .br ⟨.exit, args⟩
  | term => term

/-- Unchecked syntax transformation. The entry and exit blocks are shared with
the original lowering. Only the terminator of the header is changed. -/
def directExit (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) :
    Cfg TargetOp (Label carried result) Γ [result] :=
  let cfg := lower g
  { cfg with
    block := fun
      | .header => (cfg.block .header).mapTerm pruneTerm
      | .exit => cfg.block .exit }

/-- Emit the direct-branch CFG only when the analysis admits the rewrite. -/
def rewrite (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :
    Option (Cfg TargetOp (Label carried result) Γ [result]) :=
  if ExitOnly g facts then some (directExit g) else none

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit
