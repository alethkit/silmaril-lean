module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Defs

/-! # Checked availability for a second preheader binding -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (Program TargetOp evalOp lower)

variable {Input Γ : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

def savedHeader : BlockId (Label saved carried result) := some ⟨_, .header⟩

/-- Read the saved argument as the new preheader result, the latch as
local, and the remaining arguments as the immutable inputs. -/
def savedOrigins : Origins (saved :: Input) (saved :: carried :: Input)
  | _, .here => .inl .here
  | _, .there .here => .inr 0
  | _, .there (.there ref) => .inl (.there ref)

/-- A candidate reads the saved value and immutable inputs in this scope. -/
structure Candidate (Input : List Width) (saved carried result : Width) where
  width : Width
  args : List Width
  op : TargetOp args width
  inputs : Operands (saved :: Input) args
  operands : List (Point (Label saved carried result))
  uses : List (Use (Label saved carried result))

/-- Operand origins after capture: the saved input is defined at cut one. -/
def savedSites : {args : List Width} → Operands (saved :: Input) args →
    List (Point (Label saved carried result))
  | _, .nil => []
  | _, .cons .here tail => ⟨none, 1⟩ :: savedSites tail
  | _, .cons (.there _) tail => ⟨none, 0⟩ :: savedSites tail

/-- Read the current typed binding and require a genuine use of the already
hoisted producer. Preceding header bindings still create local origins. -/
def findCandidate? : (index cut : Nat) → {Γ : List Width} → Origins (saved :: Input) Γ →
    Block TargetOp (Label saved carried result) Γ [result] →
    Option (Candidate Input saved carried result)
  | 0, cut, _, origins, .letOp op operands rest => do
    let inputs ← captureOrigins? origins operands
    if (positions 0 inputs 0).isEmpty then none
    else pure ⟨_, _, op, inputs, savedSites inputs, useSitesAt savedHeader 0 (cut + 1) rest⟩
  | index + 1, cut, _, origins, .letOp _ _ rest =>
    findCandidate? index (cut + 1) (afterBinding origins (cut + 1)) rest
  | _, _, _, _, .terminator _ => none

/-- Return the value of the nominated binding in a single header activation. -/
def valueAt? : Nat → {Γ : List Width} → Block TargetOp (Label saved carried result) Γ [result] →
    Env Γ → Option ((w : Width) × BitVec w.val)
  | 0, _, .letOp op operands _, env => some ⟨_, evalOp op (operands.eval env)⟩
  | index + 1, _, .letOp op operands rest, env =>
    valueAt? index rest (.cons (evalOp op (operands.eval env)) env)
  | _, _, .terminator _, _ => none

def isExit (target : Target (Label saved carried result)) : Bool :=
  match target with
  | ⟨_, .exit⟩ => true
  | ⟨_, .header⟩ => false

def targetDecEq : DecidableEq (Target (Label saved carried result)) :=
  fun a b => decidable_of_iff (isExit a = isExit b)
    ⟨by rcases a with ⟨_, a⟩; rcases b with ⟨_, b⟩; cases a <;> cases b <;> simp_all [isExit],
      congrArg isExit⟩

def intermediateBlocks : List (Target (Label saved carried result)) :=
  [⟨_, .header⟩, ⟨_, .exit⟩]

def checkConsumer (cfg : Silmaril.MLIR.CF.Cfg TargetOp (Label saved carried result) Input [result])
    (candidate : Candidate Input saved carried result) : Bool :=
  let _ := targetDecEq (saved := saved) (carried := carried) (result := result)
  GCM.Dominance.Placement.checkCut cfg intermediateBlocks candidate.operands candidate.uses ⟨none, 1⟩

structure Prepared (Input : List Width) (carried result : Width) where
  intermediate : Output Input carried result
  origins : List Nat
  index : Nat
  consumer : Candidate Input intermediate.1 carried result

/-- Replay the first plan, delete the first original identity, and check the
second request at cut one of the actual intermediate preheader. -/
def prepare? (g : Program Input carried result entrySigs headerSigs)
    (first : AfterReorder.Plan) (consumerOrigin : Nat) : Option (Prepared Input carried result) := do
  let state ← Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header
  let firstIndex ← Header.Priority.resolve? state first.hoistOrigin
  let (_, intermediate) ←
    hoistCodeWith? state.cfg.entry (state.cfg.block .header) firstIndex (chooseCfgCut? state.cfg)
  let origins := state.origins.eraseIdx firstIndex
  let index ← origins.idxOf? consumerOrigin
  let consumer ← findCandidate? index 0 savedOrigins (intermediate.2.block .header)
  if checkConsumer intermediate.2 consumer then
    pure ⟨intermediate, origins, index, consumer⟩
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
