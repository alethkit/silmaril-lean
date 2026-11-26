module

public import Init.Data.List.MinMaxOn
public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Defs

/-! # The common-dominator bound for Schedule Late -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LatePlacement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

/-- Resolve each use at its existing read cut and retain the original occurrence.
In particular, two Phi slots at one source stay distinct at that cut. -/
def resolveUses? (tree : DominatorTree cfg) : List (Use Label) →
    Option (List (Use Label × Point Label))
  | [] => some []
  | use :: rest => do
    let read ← use.point? cfg
    if read.valid? tree then
      let sites ← resolveUses? tree rest
      return (use, read) :: sites
    else none

/-- Enumerate the represented reachable blocks whose addresses prefix every read address. -/
def commonDominators (tree : DominatorTree cfg) (blocks : List (Target Label))
    (sites : List (Use Label × Point Label)) : List (BlockId Label) :=
  (NaturalLoop.vertices blocks).filter fun block =>
    tree.reachable block && sites.all fun site =>
      (tree.address block).isPrefixOf (tree.address site.2.block)

/-- Find the deepest common dominator of a nonempty, valid list of uses.
An empty list or an invalid use has no late bound. `some none` denotes entry. -/
def lateBound? (tree : DominatorTree cfg) (blocks : List (Target Label))
    (uses : List (Use Label)) : Option (BlockId Label) := do
  let sites ← resolveUses? tree uses
  if sites.isEmpty then none
  else (commonDominators tree blocks sites).maxOn? fun block => (tree.address block).length

end Silmaril.SSA.SeaOfNodes.GCM.LatePlacement
