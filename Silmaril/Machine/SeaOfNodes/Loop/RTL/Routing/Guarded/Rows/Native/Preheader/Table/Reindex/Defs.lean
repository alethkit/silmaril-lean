module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Defs

/-! Typed capture permutations for checked dependent preheaders. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)

variable {arity : Nat} {entrySigs sigs : List (List PortTy)}

/-- Reindex capture reads in each producer's typed prefix. -/
def reindexFlow (perm : InputPermutation arity) : {past sigs : List (List PortTy)} →
    Dataflow WordOp (wordPorts arity) past sigs → Dataflow WordOp (wordPorts arity) past sigs
  | _, _, .nil => .nil
  | _, _, .cons op args rest => .cons op (perm.column args) (reindexFlow perm rest)

/-- Permute capture reads in the preheader and entry column. The checked
header reads its bank and local producers. Its backedge and exit stay in
their original scope and occurrence. -/
def reindexCaptures (perm : InputPermutation arity) (g : SourceWithEntry arity entrySigs sigs) :
    SourceWithEntry arity entrySigs sigs :=
  { g with
    preheader := reindexFlow perm g.preheader
    phiInputs
      | .entry => perm.column (g.phiInputs .entry)
      | .backedge => g.phiInputs .backedge }

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
