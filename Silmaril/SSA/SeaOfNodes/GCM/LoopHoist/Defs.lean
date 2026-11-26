module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs

/-! # Hoist the first invariant binding of the existing pure typed loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.SCF (For)
open Loop.MLIR.CF (Program TargetOp lower)

abbrev SourceLabel := Loop.MLIR.CF.Label

/-- The header receives the saved result first, then the original latch word. -/
inductive Label (saved carried result : Width) : List Width → Type where
  | header : Label saved carried result [saved, carried]
  | exit : Label saved carried result [result]

abbrev Output (Input : List Width) (carried result : Width) :=
  (saved : Width) × Cfg TargetOp (Label saved carried result) Input [result]

variable {Input Γ Δ args : List Width} {saved carried result w : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

def headerId : BlockId (SourceLabel carried result) := some ⟨_, .header⟩

def blocks : List (Target (SourceLabel carried result)) := [⟨_, .header⟩, ⟨_, .exit⟩]

/-- At header entry, index zero is the latch. Larger indices are immutable
function inputs, already available at preheader cut zero. -/
def operandSites : {args : List Width} → Operands (carried :: Input) args → List (Point (SourceLabel carried result))
  | _, .nil => []
  | _, .cons ref tail =>
    ⟨if ref.index == 0 then headerId else none, 0⟩ :: operandSites tail

/-- Translate a header operand list to entry scope when it reads only captures. -/
def capture? : {args : List Width} → Operands (carried :: Input) args → Option (Operands Input args)
  | _, .nil => some .nil
  | _, .cons .here _ => none
  | _, .cons (.there ref) tail => (capture? tail).map (.cons ref)

def positions (index : Nat) : {args : List Width} → Operands Γ args → Nat → List Nat
  | _, .nil, _ => []
  | _, .cons ref rest, slot =>
    let later := positions index rest (slot + 1)
    if ref.index == index then slot :: later else later

def useSites (index cut : Nat) : {Γ : List Width} →
    Block TargetOp (SourceLabel carried result) Γ [result] → List (Use (SourceLabel carried result))
  | _, .letOp _ operands rest =>
    let later := useSites (index + 1) (cut + 1) rest
    if (positions index operands 0).isEmpty then later else .ordinary ⟨headerId, cut⟩ :: later
  | _, .terminator (.br edge) =>
    (positions index edge.args 0).map (.phi headerId .jump)
  | _, .terminator (.condBr test onTrue onFalse) =>
    let guard := if test.index == index then [.ordinary ⟨headerId, cut⟩] else []
    guard ++ (positions index onTrue.args 0).map (.phi headerId .onTrue) ++
      (positions index onFalse.args 0).map (.phi headerId .onFalse)
  | _, .terminator (.ret values) =>
    if (positions index values 0).isEmpty then [] else [.ordinary ⟨headerId, cut⟩]

abbrev Rename (Γ Δ : List Width) := ∀ {w}, Var Γ w → Var Δ w

def under (rename : Rename Γ Δ) : Rename (w :: Γ) (w :: Δ)
  | _, .here => .here
  | _, .there ref => .there (rename ref)

def routeEdge (rename : Rename Γ Δ) (keep : Var Δ saved) :
    Edge (SourceLabel carried result) Γ → Edge (Label saved carried result) Δ
  | ⟨.header, args⟩ => ⟨.header, .cons keep (For.renameOperands rename args)⟩
  | ⟨.exit, args⟩ => ⟨.exit, For.renameOperands rename args⟩

def routeTerm (rename : Rename Γ Δ) (keep : Var Δ saved) :
    Terminator (SourceLabel carried result) [result] Γ →
      Terminator (Label saved carried result) [result] Δ
  | .br edge => .br (routeEdge rename keep edge)
  | .condBr test onTrue onFalse =>
    .condBr (rename test) (routeEdge rename keep onTrue) (routeEdge rename keep onFalse)
  | .ret values => .ret (For.renameOperands rename values)

def routeCode : {Γ Δ : List Width} → Rename Γ Δ → Var Δ saved →
    Block TargetOp (SourceLabel carried result) Γ [result] →
      Block TargetOp (Label saved carried result) Δ [result]
  | _, _, rename, keep, .terminator term => .terminator (routeTerm rename keep term)
  | _, _, rename, keep, .letOp op operands rest =>
    .letOp op (For.renameOperands rename operands) (routeCode (under rename) (.there keep) rest)

/-- The entry gets one new binding. The old first header binding becomes
a parameter in exactly the same lexical position for the remainder. -/
def emit (entry : Block TargetOp (SourceLabel carried result) Input [result])
    (op : TargetOp args saved) (captured : Operands Input args)
    (rest : Block TargetOp (SourceLabel carried result) (saved :: carried :: Input) [result]) :
    Cfg TargetOp (Label saved carried result) Input [result] where
  entry := .letOp op captured (routeCode Var.there .here entry)
  block
    | .header => routeCode (fun ref => ref) .here rest
    | .exit => .terminator (.ret (.cons .here .nil))

def carryFrame (value : BitVec saved.val) :
    Frame (SourceLabel carried result) → Frame (Label saved carried result)
  | ⟨.header, args⟩ => ⟨.header, .cons value args⟩
  | ⟨.exit, args⟩ => ⟨.exit, args⟩

/-- Rank the actual source cuts with the checked natural-loop depth. The
only supported destination is cut zero of the existing preheader. -/
def pickAndHoist? (g : Program Input carried result entrySigs headerSigs)
    (tree : DominatorTree (lower g)) : Option (Point (SourceLabel carried result) × Output Input carried result) :=
  match (lower g).block .header with
  | .terminator _ => none
  | .letOp (w := saved) op operands rest => do
    let cut ← LoopForest.choosePlacement tree blocks (operandSites operands) (useSites 0 1 rest)
    if cut.block.isNone && cut.cut == 0 then
      let captured ← capture? operands
      pure (cut, ⟨saved, emit (lower g).entry op captured rest⟩)
    else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
