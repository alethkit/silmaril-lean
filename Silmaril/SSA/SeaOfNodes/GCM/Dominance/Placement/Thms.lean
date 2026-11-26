module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {blocks : List (Target Label)}
variable {operands : List (Point Label)} {uses : List (Use Label)} {candidate : Point Label}
variable [DecidableEq (Target Label)]

/-- The executable check characterizes the existing cut legality predicate
when the finite inventory covers every successor of entry and listed blocks. -/
theorem checkCut_iff : checkCut cfg blocks operands uses candidate = true ↔
    checkClosed cfg blocks = true ∧ Legal cfg operands uses candidate :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement.checkCut_iff

/-- A discovered cut is in the enumeration and is legal on the typed CFG. -/
theorem discoverCut_sound (found : discoverCut cfg blocks operands uses = some candidate) :
    candidate ∈ candidateCuts cfg blocks ∧
      checkClosed cfg blocks = true ∧ Legal cfg operands uses candidate :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement.discoverCut_sound found

/-- Closure makes the enumeration include every reachable and in-bounds
cut, so failure rules out every legal cut of the CFG. -/
theorem discoverCut_eq_none_iff (closed : checkClosed cfg blocks = true) :
    discoverCut cfg blocks operands uses = none ↔
      ∀ point, ¬ Legal cfg operands uses point :=
  Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement.discoverCut_eq_none_iff closed

end Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement
