module

public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.MLIR.Defs
public import Silmaril.SSA.MLIR.SCF.For.Defs

/-! Lower a ranked pure single loop with one word latch to typed MLIR CF. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF

open Diamond (ValueSort dataPorts)
open RVSDG (Tuple extend)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (Scope OpcodeMap inputNames lowerCode weaken)
open Silmaril.MLIR.Arith (BinOp Width)
open Silmaril.MLIR.Pure (Eval OpSignature)
open Silmaril.MLIR.CF (Cfg Terminator)
open Silmaril.MLIR.SCF (For)

/-- Reuse the source arithmetic operations and add an unsigned comparison. -/
inductive Op : Diamond.Signature Width where
  | arithmetic {ins out} : SeaOfNodes.MLIR.Op ins out → Op ins out
  | ult (w : Width) : Op [.data w, .data w] .predicate

abbrev model : Diamond.Model Op where
  value := Word
  run
    | .arithmetic op, args => SeaOfNodes.MLIR.model.run op args
    | .ult _, .cons x (.cons y .nil) => ⟨x.ult y⟩

/-- The constant and flag-free arithmetic symbols used in the emitted code. -/
inductive WordOp : OpSignature where
  | constant {w : Width} (bits : Word w) : WordOp [] w
  | binary (w : Width) (op : BinOp) : WordOp [w, w] w

def evalWord : Eval WordOp
  | _, _, .constant bits, .nil => bits
  | _, _, .binary _ op, .cons x (.cons y .nil) => op.denote x y

/-- Use the existing `arith.cmpi ult` interpreter from the scalar SCF lowering. -/
abbrev TargetOp := For.LowerOp WordOp

def evalOp : Eval TargetOp := For.lowerEval evalWord

def opcode : OpcodeMap Op TargetOp
  | _, _, .arithmetic (.constant bits) => .original (.constant bits)
  | _, _, .arithmetic (.binary (w := w) op) => .original (.binary w op)
  | _, _, .ult w => .ult w

abbrev inputSorts (Γ : List Width) : List (ValueSort Width) :=
  Γ.map ValueSort.data

abbrev Program (Γ : List Width) (carried result : Width)
    (entrySigs headerSigs : List (List (Diamond.Ty Width))) :=
  Loop.Graph Op (inputSorts Γ) [.data carried] entrySigs headerSigs (.data result)

inductive Label (carried result : Width) : List Width → Type where
  | header : Label carried result [carried]
  | exit : Label carried result [result]

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

def entryScope (Γ : List Width) : Scope (dataPorts (inputSorts Γ)) [] Γ :=
  ⟨inputNames Γ, PUnit.unit⟩

/-- Block arguments are first in the CF scope. Source header ports put the
captured inputs first and the old latch last. -/
def headerScope (Γ : List Width) (carried : Width) :
    Scope (headerPorts (inputSorts Γ) [.data carried]) [] (carried :: Γ) :=
  ⟨appendTuple (.cons .here .nil) ((inputNames Γ).map (weaken carried)), PUnit.unit⟩

variable (g : Program Γ carried result entrySigs headerSigs)

def entryTerm {Δ : List Width} (scope : Scope (dataPorts (inputSorts Γ)) (extend [] entrySigs) Δ) :
    Terminator (Label carried result) [result] Δ :=
  .br ⟨.header, .cons (scope.resolveValue ((g.phiInputs .entry).get .head)) .nil⟩

def headerTerm {Δ : List Width}
    (scope : Scope (headerPorts (inputSorts Γ) [.data carried]) (extend [] headerSigs) Δ) :
    Terminator (Label carried result) [result] Δ :=
  .condBr (scope.resolveValue g.predicate)
    ⟨.header, .cons (scope.resolveValue ((g.phiInputs .backedge).get .head)) .nil⟩
    ⟨.exit, .cons (scope.resolveValue g.result) .nil⟩

/-- Emit the preheader, a self-branching header, and a distinct exit block.
The branch passes either the backedge Phi operand or the selected result. -/
def lower : Cfg TargetOp (Label carried result) Γ [result] where
  entry := lowerCode opcode g.preheader (entryScope Γ) (entryTerm g)
  block
    | .header => lowerCode opcode g.header (headerScope Γ carried) (headerTerm g)
    | .exit => .terminator (.ret (.cons .here .nil))

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF
