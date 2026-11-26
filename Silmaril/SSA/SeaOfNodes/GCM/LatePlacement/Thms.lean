module

public import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LatePlacement.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LatePlacement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Dominance (checkClosed)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {tree : DominatorTree cfg}
variable {blocks : List (Target Label)} {uses : List (Use Label)}
variable {sites : List (Use Label × Point Label)} {late : BlockId Label}

/-- Successful resolution preserves the input occurrences in order and pairs
every occurrence with its valid CFG read cut. -/
theorem resolveUses?_spec (resolved : resolveUses? tree uses = some sites) :
    sites.map Prod.fst = uses ∧
      ∀ site ∈ sites, site.1.point? cfg = some site.2 ∧ site.2.Valid cfg :=
  Proofs.SSA.SeaOfNodes.GCM.LatePlacement.resolveUses?_spec resolved

/-- Complete evidence gives a bound exactly for nonempty valid use lists. -/
theorem lateBound?_isSome_iff (complete : tree.Complete) :
    (lateBound? tree blocks uses).isSome = true ↔
      uses ≠ [] ∧ ∀ use ∈ uses, ∃ read, use.point? cfg = some read ∧ read.Valid cfg :=
  Proofs.SSA.SeaOfNodes.GCM.LatePlacement.lateBound?_isSome_iff complete

variable [DecidableEq (Target Label)]

/-- A block dominates the computed bound exactly when it dominates every
use's resolved read block. The bound is reachable. -/
theorem lateBound?_spec (complete : tree.Complete) (closed : checkClosed cfg blocks = true)
    (found : lateBound? tree blocks uses = some late) :
    Reachable cfg late ∧ ∀ block,
      Dominates cfg block late ↔
        ∀ use ∈ uses, ∃ read, use.point? cfg = some read ∧ Dominates cfg block read.block :=
  Proofs.SSA.SeaOfNodes.GCM.LatePlacement.lateBound?_spec complete closed found

/-- In the existing legal corridor, the late bound summarizes use-block
dominance. Operand availability and local cut order are checked as before. -/
theorem legal_iff_lateBound (complete : tree.Complete) (closed : checkClosed cfg blocks = true)
    (found : lateBound? tree blocks uses = some late)
    (operands : List (Point Label)) (candidate : Point Label) :
    Legal cfg operands uses candidate ↔
      candidate.Valid cfg ∧
      (∀ operand ∈ operands, operand.Valid cfg ∧ operand.AvailableAt cfg candidate) ∧
      Dominates cfg candidate.block late ∧
      ∀ use ∈ uses, ∀ read, use.point? cfg = some read →
        candidate.block = read.block → candidate.cut ≤ read.cut :=
  Proofs.SSA.SeaOfNodes.GCM.LatePlacement.legal_iff_lateBound complete closed found operands candidate

end Silmaril.SSA.SeaOfNodes.GCM.LatePlacement
