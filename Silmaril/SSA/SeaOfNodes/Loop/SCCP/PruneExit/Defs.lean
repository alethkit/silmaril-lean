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

/-- The simultaneous solution marks the chosen successor and excludes the other. -/
def OnlySuccessor (feedback : Bool) (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs)
    (facts : InputFacts Γ) : Prop :=
  let edges := (solve model g facts).1
  let backedge := incomingIndex .backedge
  (if feedback then backedge else exitIndex) ∈ edges ∧
    (if feedback then exitIndex else backedge) ∉ edges

instance (feedback : Bool) (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs)
    (facts : InputFacts Γ) : Decidable (OnlySuccessor feedback g facts) := by
  unfold OnlySuccessor
  infer_instance

abbrev ExitOnly := @OnlySuccessor Γ carried result entrySigs headerSigs false

def isHeader {args : List Width} : Loop.MLIR.CF.Bank.Label carried result args → Bool
  | .header => true
  | .exit => false

/-- Keep the selected edge and its exact operands in the emitted header shape. -/
def selectTerm {Δ : List Width} (feedback : Bool) :
    Terminator (Loop.MLIR.CF.Bank.Label carried result) [result] Δ →
    Terminator (Loop.MLIR.CF.Bank.Label carried result) [result] Δ
  | .condBr test yes no =>
    if isHeader yes.label && !isHeader no.label then .br (if feedback then yes else no)
    else .condBr test yes no
  | term => term

abbrev pruneTerm {Δ : List Width} :=
  @selectTerm carried result Δ false

/-- Change only the header terminator of the emitted loop. -/
def selectHeader (feedback : Bool) (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) :
    Cfg TargetOp (Loop.MLIR.CF.Bank.Label carried result) Γ [result] :=
  let cfg := Loop.MLIR.CF.Bank.lower g
  { cfg with
    block := fun
      | .header => (cfg.block .header).mapTerm (selectTerm feedback)
      | .exit => cfg.block .exit }

/-- Emit the direct branch only when the analysis admits the rewrite. -/
def rewriteSelected (feedback : Bool) (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs)
    (facts : InputFacts Γ) : Option (Cfg TargetOp (Loop.MLIR.CF.Bank.Label carried result) Γ [result]) :=
  if OnlySuccessor feedback g facts then some (selectHeader feedback g) else none

abbrev directExit := @selectHeader Γ carried result entrySigs headerSigs false
abbrev rewrite := @rewriteSelected Γ carried result entrySigs headerSigs false

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
