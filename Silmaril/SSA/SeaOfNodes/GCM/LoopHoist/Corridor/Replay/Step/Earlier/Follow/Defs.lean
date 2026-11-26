module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Defs

/-! # One checked follow-on placement on a permuted saved prefix -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.SCF (For)
open AfterReorder.Second (Candidate checkPrefixCut)
open AfterReorder.Second.Emit (liftCode)
open Loop.MLIR.CF (TargetOp)

variable {Input extra : List Width} {saved carried result : Width}

abbrev CurrentExtra (prior : Earlier.Emission Input saved carried result extra) :=
  prior.append.candidate.width :: extra

def savedCount (prior : Earlier.Emission Input saved carried result extra) : Nat :=
  prior.splice.physical.length - Input.length

/-- Definition sites in the actual physical prefix. Immutable input
    references lie past the saved definitions and have cut zero. -/
def physicalSites {Γ : List Width} (count : Nat) : {args : List Width} → Operands Γ args →
    List (Point (Label saved carried result extra))
  | _, .nil => []
  | _, .cons ref rest => ⟨none, count - ref.index⟩ :: physicalSites count rest

def physicalOperands (prior : Earlier.Emission Input saved carried result extra)
    (candidate : Candidate Input saved carried result (CurrentExtra prior)) :
    Operands prior.splice.physical candidate.args :=
  For.renameOperands prior.splice.toPhysical candidate.inputs

/-- Keep the captured binding and its exact ordinary and Φ uses, replacing
    only definition sites by the positions of the actual routed operands. -/
def atLayout (prior : Earlier.Emission Input saved carried result extra)
    (candidate : Candidate Input saved carried result (CurrentExtra prior)) :
    Candidate Input saved carried result (CurrentExtra prior) :=
  { candidate with operands := physicalSites (savedCount prior) (physicalOperands prior candidate) }

structure Emission (prior : Earlier.Emission Input saved carried result extra) where
  append : Step.Emission Input saved carried result (CurrentExtra prior)
  splice : Saved.Prefix.Insertion Input prior.splice.physical append.candidate.width

def Emission.cfg {prior : Earlier.Emission Input saved carried result extra} (moved : Emission prior) :
    Cfg TargetOp (Label saved carried result (moved.append.candidate.width :: CurrentExtra prior)) Input [result] :=
  { moved.append.next.cfg with
    entry := moved.splice.leading.wrap (liftCode moved.splice.previous moved.splice.inserted prior.entryTail) }

/-- Resolve the origin on the surviving header shared with the append
    reference. Check the requested cut on the actual permuted CFG, then
    splice the physically renamed operands into its prefix. -/
def emit? (prior : Earlier.Emission Input saved carried result extra) (request : Nomination) :
    Option (Emission prior) := do
  let endCut := ((CurrentExtra prior) ++ [saved]).length
  let .ok append := Step.emit prior.append.next { request with cut := endCut } | none
  if checkPrefixCut prior.cfg (atLayout prior append.candidate) request.cut then
    let splice ← prior.splice.leading.insert? append.candidate.op (savedCount prior - request.cut)
      (physicalOperands prior append.candidate)
    pure ⟨append, splice⟩
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow
