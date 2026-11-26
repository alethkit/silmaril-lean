module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs

/-! # Hoist an invariant binding of the existing pure typed loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.SCF (For)
open Loop.MLIR.CF (Program TargetOp evalOp lower)

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

def emitHeader (entry : Block TargetOp (SourceLabel carried result) Input [result])
    (op : TargetOp args saved) (captured : Operands Input args)
    (header : Block TargetOp (Label saved carried result) (saved :: carried :: Input) [result]) :
    Cfg TargetOp (Label saved carried result) Input [result] where
  entry := .letOp op captured (routeCode Var.there .here entry)
  block
    | .header => header
    | .exit => .terminator (.ret (.cons .here .nil))

/-- The old first header binding becomes a parameter for the remainder. -/
def emit (entry : Block TargetOp (SourceLabel carried result) Input [result])
    (op : TargetOp args saved) (captured : Operands Input args)
    (rest : Block TargetOp (SourceLabel carried result) (saved :: carried :: Input) [result]) :
    Cfg TargetOp (Label saved carried result) Input [result] :=
  emitHeader entry op captured (routeCode (fun ref => ref) .here rest)

def carryFrame (value : BitVec saved.val) :
    Frame (SourceLabel carried result) → Frame (Label saved carried result)
  | ⟨.header, args⟩ => ⟨.header, .cons value args⟩
  | ⟨.exit, args⟩ => ⟨.exit, args⟩

/-- The emitted entry and each block reproduce the source transfer, with
the same saved value prepended to the header arguments. -/
structure Routes (source : Cfg TargetOp (SourceLabel carried result) Input [result])
    (target : Cfg TargetOp (Label saved carried result) Input [result])
    (input : Env Input) (value : BitVec saved.val) : Prop where
  entry :
    target.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      (source.entry.eval evalOp (fun term env => Terminator.eval env term) input).map (carryFrame value) id
  block : ∀ frame : Frame (SourceLabel carried result),
    let routed := carryFrame value frame
    (target.block routed.label).eval evalOp (fun term env => Terminator.eval env term)
      (routed.args.append input) =
      ((source.block frame.label).eval evalOp (fun term env => Terminator.eval env term)
        (frame.args.append input)).map (carryFrame value) id

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

/-- An in-scope variable names either an immutable input or a local definition.
The local number is the cut after the defining binding, with zero for the latch. -/
abbrev Origins (Input Γ : List Width) := ∀ {w}, Var Γ w → Var Input w ⊕ Nat

def headerOrigins : Origins Input (carried :: Input)
  | _, .here => .inr 0
  | _, .there ref => .inl ref

def afterBinding (origins : Origins Input Γ) (cut : Nat) : Origins Input (w :: Γ)
  | _, .here => .inr cut
  | _, .there ref => origins ref

def originSites (origins : Origins Input Γ) : {args : List Width} →
    Operands Γ args → List (Point (SourceLabel carried result))
  | _, .nil => []
  | _, .cons ref rest =>
    let site := match origins ref with
      | .inl _ => ⟨none, 0⟩
      | .inr cut => ⟨headerId, cut⟩
    site :: originSites origins rest

/-- Translate only directly captured operands, rejecting a read of any local result. -/
def captureOrigins? (origins : Origins Input Γ) :
    {args : List Width} → Operands Γ args → Option (Operands Input args)
  | _, .nil => some .nil
  | _, .cons ref rest =>
    match origins ref with
    | .inl input => (captureOrigins? origins rest).map (.cons input)
    | .inr _ => none

def replaceBinding (rename : Rename Γ Δ) (keep : Var Δ saved) : Rename (saved :: Γ) Δ
  | _, .here => keep
  | _, .there ref => rename ref

/-- A binding found in an existing typed block, with its sites and an emitter
for the block with that binding replaced by a reference to the saved value. -/
structure Binding (Input Γ : List Width) (saved carried result : Width) where
  args : List Width
  op : TargetOp args saved
  captured? : Option (Operands Input args)
  operands : List (Point (SourceLabel carried result))
  uses : List (Use (SourceLabel carried result))
  rewrite : ∀ {Δ : List Width}, Rename Γ Δ → Var Δ saved →
    Block TargetOp (Label saved carried result) Δ [result]

def Binding.prepend (op : TargetOp args w) (operands : Operands Γ args)
    (binding : Binding Input (w :: Γ) saved carried result) : Binding Input Γ saved carried result where
  args := binding.args
  op := binding.op
  captured? := binding.captured?
  operands := binding.operands
  uses := binding.uses
  rewrite rename keep := .letOp op (For.renameOperands rename operands)
    (binding.rewrite (under rename) (.there keep))

/-- Find a zero-based binding index and preserve the prefix in its original
order. Only the nominated let is removed. -/
def findBinding : (index cut : Nat) → {Γ : List Width} → Origins Input Γ →
    Block TargetOp (SourceLabel carried result) Γ [result] →
    Option ((saved : Width) × Binding Input Γ saved carried result)
  | _, _, _, _, .terminator _ => none
  | 0, cut, _, origins, .letOp (w := saved) op operands rest =>
    some ⟨saved, ⟨_, op, captureOrigins? origins operands, originSites origins operands,
      useSites 0 (cut + 1) rest, fun rename keep => routeCode (replaceBinding rename keep) keep rest⟩⟩
  | index + 1, cut, _, origins, .letOp op operands rest =>
    (findBinding index (cut + 1) (afterBinding origins (cut + 1)) rest).map
      fun ⟨saved, binding⟩ => ⟨saved, binding.prepend op operands⟩

/-- Hoist the nominated binding when its exact use sites and operand origins
lead the loop ranker to preheader cut zero and the operands are captured inputs. -/
def pickBindingAndHoist? (g : Program Input carried result entrySigs headerSigs)
    (tree : DominatorTree (lower g)) (index : Nat) :
    Option (Point (SourceLabel carried result) × Output Input carried result) := do
  let ⟨saved, binding⟩ ← findBinding index 0 headerOrigins ((lower g).block .header)
  let cut ← LoopForest.choosePlacement tree blocks binding.operands binding.uses
  if cut.block.isNone && cut.cut == 0 then
    let captured ← binding.captured?
    let header := binding.rewrite Var.there .here
    pure (cut, ⟨saved, emitHeader (lower g).entry binding.op captured header⟩)
  else none


end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
