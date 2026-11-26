module

public import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Defs

/-! # Schedule Late on a typed diamond with parallel Phi occurrences -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)

inductive Label : List Width → Type
  | fork : Label [i1]
  | left : Label [i1]
  | right : Label [i1]
  | join : Label [i1]
  | dead : Label []
  deriving DecidableEq

def target {params : List Width} (label : Label params) : Target Label := ⟨params, label⟩
def block {params : List Width} (label : Label params) : BlockId Label := some (target label)

def cfg : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.br ⟨.fork, .cons .here .nil⟩)
  block
    | .fork =>
      .terminator (.condBr .here ⟨.left, .cons .here .nil⟩ ⟨.right, .cons .here .nil⟩)
    | .left => .letOp (w := i1) () .nil (.terminator
        (.condBr .here ⟨.join, .cons .here .nil⟩ ⟨.join, .cons (.there .here) .nil⟩))
    | .right => .terminator (.br ⟨.join, .cons .here .nil⟩)
    | .join => .terminator (.ret (.cons .here .nil))
    | .dead => .terminator (.br ⟨.join, .cons .here .nil⟩)

def blocks : List (Target Label) :=
  [target .dead, target .join, target .right, target .left, target .fork]

def number : BlockId Label → Nat
  | none => 0
  | some ⟨_, .fork⟩ => 1
  | some ⟨_, .left⟩ => 2
  | some ⟨_, .right⟩ => 3
  | some ⟨_, .join⟩ => 4
  | some ⟨_, .dead⟩ => 5

private theorem number_injective : Function.Injective number := by
  rintro (_ | ⟨_, a⟩) (_ | ⟨_, b⟩)
  · intro _
    rfl
  · cases b <;> simp [number]
  · cases a <;> simp [number]
  · cases a <;> cases b <;> simp [number]

def tree? : Option {tree : DominatorTree cfg // tree.Complete} :=
  Dominance.Tree.Synthesis.synthesize? cfg blocks number (by exact number_injective)

def parallelUses : List (Use Label) :=
  [.phi (block .left) .onTrue 0, .phi (block .left) .onFalse 0]

def bothArms : List (Use Label) := .phi (block .right) .jump 0 :: parallelUses

/-- The first bound is for the parallel left edges. The second also includes
the incoming edge from the right arm. -/
def bounds : Option (BlockId Label × BlockId Label) := do
  let tree ← tree?
  let left ← lateBound? tree.1 blocks parallelUses
  let across ← lateBound? tree.1 blocks bothArms
  return (left, across)

end Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Example
