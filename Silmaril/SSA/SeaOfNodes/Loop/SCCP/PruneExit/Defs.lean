module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Thms

/-! Delete the infeasible backedge from the emitted MLIR loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit

open Diamond (Val dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)
open SeaOfNodes.MLIR (Word)
open Loop.MLIR.CF (Label TargetOp model inputSorts)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Terminator)

abbrev InputFacts (Γ : List Width) :=
  Tuple (Fact model.value) (dataPorts (inputSorts Γ))

namespace Bank

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Each carried coordinate compares words at its own width. -/
@[instance_reducible]
def wordBankEq : (widths : List Width) → BankDecidableEq model.value (dataPorts (inputSorts widths))
  | [] => ⟨fun i => i.elim0⟩
  | w :: rest =>
    ⟨fun i => Fin.cases (motive := fun j =>
      DecidableEq (Val model.value (dataPorts (inputSorts (w :: rest)))[j]))
      (inferInstance : DecidableEq (Word w)) ((wordBankEq rest).atPort) i⟩

instance (widths : List Width) : BankDecidableEq model.value (dataPorts (inputSorts widths)) :=
  wordBankEq widths

/-- Require a marked exit and an unmarked backedge at the simultaneous fixed point. -/
def ExitOnly (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) : Prop :=
  let edges := (solve model g facts).1
  exitIndex ∈ edges ∧ incomingIndex .backedge ∉ edges

instance (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :
    Decidable (ExitOnly g facts) :=
  inferInstanceAs (Decidable (exitIndex ∈ (solve model g facts).1 ∧
    incomingIndex .backedge ∉ (solve model g facts).1))

def isHeader {args : List Width} : Loop.MLIR.CF.Bank.Label carried result args → Bool
  | .header => true
  | .exit => false

/-- Specialize the header conditional using its exact false edge and operands. -/
def pruneTerm {Δ : List Width} : Terminator (Loop.MLIR.CF.Bank.Label carried result) [result] Δ →
    Terminator (Loop.MLIR.CF.Bank.Label carried result) [result] Δ
  | .condBr test yes no =>
    if isHeader yes.label && !isHeader no.label then .br no else .condBr test yes no
  | term => term

/-- Unchecked syntax transformation. The entry and exit blocks are shared with
the original lowering. Only the terminator of the header is changed. -/
def directExit (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) :
    Cfg TargetOp (Loop.MLIR.CF.Bank.Label carried result) Γ [result] :=
  let cfg := Loop.MLIR.CF.Bank.lower g
  { cfg with
    block := fun
      | .header => (cfg.block .header).mapTerm pruneTerm
      | .exit => cfg.block .exit }

/-- Emit the direct-branch CFG only when the analysis admits the rewrite. -/
def rewrite (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :
    Option (Cfg TargetOp (Loop.MLIR.CF.Bank.Label carried result) Γ [result]) :=
  if ExitOnly g facts then some (directExit g) else none

end Bank

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

instance wordBankEq (w : Width) : BankDecidableEq model.value (dataPorts [.data w]) :=
  Bank.wordBankEq [w]

abbrev ExitOnly (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :=
  Bank.ExitOnly g facts

abbrev pruneTerm {Δ : List Width} (term : Terminator (Label carried result) [result] Δ) :=
  Bank.pruneTerm term

abbrev directExit (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) := Bank.directExit g

abbrev rewrite (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :=
  Bank.rewrite g facts

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit
