module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Defs

/-! # GCM cut legality from computed structural dominance -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable [DecidableEq (Target Label)]

/-- Check a cut from the CFG and its finite block inventory. Same-block
availability uses the local cut order, and Phi operands use their source slot. -/
def checkCut (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (operands : List (Point Label)) (uses : List (Use Label)) (candidate : Point Label) : Bool :=
  let valid := fun (point : Point Label) =>
    reachable? cfg blocks point.block && decide (point.cut ≤ (shape cfg point.block).bindings)
  let available := fun (defSite read : Point Label) =>
    dominates? cfg blocks defSite.block read.block &&
      decide (defSite.block = read.block → defSite.cut ≤ read.cut)
  checkClosed cfg blocks && checkPlacementWith cfg valid available operands uses candidate

/-- Search the existing cut inventory in its enumeration order. -/
def discoverCut (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (operands : List (Point Label)) (uses : List (Use Label)) : Option (Point Label) :=
  (candidateCuts cfg blocks).find? (checkCut cfg blocks operands uses)

end Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement
