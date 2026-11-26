module

import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance
open Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis

private inductive Label : List Width → Type
  | left : Label [i1]
  | right : Label [i1]
  | header : Label [i1]
  | latch : Label [i1]
  | exit : Label [i1]
  | dead : Label []
  | outside : Label []
  deriving DecidableEq

private def target {params : List Width} (label : Label params) : Target Label := ⟨params, label⟩
private def block {params : List Width} (label : Label params) : BlockId Label := some (target label)

private def cfg : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.condBr .here ⟨.left, .cons .here .nil⟩ ⟨.right, .cons .here .nil⟩)
  block
    | .left | .right => .terminator (.br ⟨.header, .cons .here .nil⟩)
    | .header => .terminator (.condBr .here ⟨.latch, .cons .here .nil⟩ ⟨.exit, .cons .here .nil⟩)
    | .latch => .terminator (.condBr .here ⟨.header, .cons .here .nil⟩
        ⟨.header, .cons (.there .here) .nil⟩)
    | .dead => .terminator (.br ⟨.exit, .cons .here .nil⟩)
    | .exit => .terminator (.ret (.cons .here .nil))
    | .outside => .terminator (.ret (.cons .here .nil))

private def blocks : List (Target Label) :=
  [target .dead, target .exit, target .latch, target .header, target .right, target .left]

private def number : BlockId Label → Nat
  | none => 0
  | some ⟨_, .left⟩ => 1
  | some ⟨_, .right⟩ => 2
  | some ⟨_, .header⟩ => 3
  | some ⟨_, .latch⟩ => 4
  | some ⟨_, .exit⟩ => 5
  | some ⟨_, .dead⟩ => 6
  | some ⟨_, .outside⟩ => 7

private theorem number_injective : Function.Injective number := by
  rintro (_ | ⟨_, a⟩) (_ | ⟨_, b⟩)
  · intro _; rfl
  · cases b <;> simp [number]
  · cases a <;> simp [number]
  · cases a <;> cases b <;> simp [number]

-- The header is the diamond join. Its parent is entry, while the latch
-- and the loop exit both have the header as their parent.
example : ([none, block .left, block .right, block .header, block .latch, block .exit,
    block .dead, block .outside].map (immediateParent? cfg blocks)) =
    [none, some none, some none, some none, some (block .header), some (block .header),
      none, none] := by cbv

example : occurrences cfg (block .latch) = [(.onTrue, target .header), (.onFalse, target .header)] :=
  by cbv

private def phiReads : List (Use Label) :=
  [.phi (block .latch) .onTrue 0, .phi (block .latch) .onFalse 0]

-- The generated certificate goes through the existing cut checker for the
-- two occurrences carrying different operands. The left arm cannot cover them.
private def placements (tree : DominatorTree cfg) : Bool × Bool × Bool :=
  let operands : List (Point Label) := [⟨none, 0⟩]
  (checkPlacement tree operands phiReads ⟨block .header, 0⟩,
    checkPlacement tree operands phiReads ⟨block .left, 0⟩,
    checkPlacement tree [] [] ⟨block .dead, 0⟩)

example : (synthesize? cfg blocks number number_injective).map (fun tree =>
    (placements tree.1, tree.1.reachable (block .dead), tree.1.reachable (block .outside),
      tree.1.address (block .dead), tree.1.address (block .outside))) =
    some ((true, false, false), false, false, [0, 6], [0, 7]) := by cbv

-- The inventory may repeat a label.
example : (synthesize? cfg (target .header :: blocks) number number_injective).isSome = true :=
  by cbv

example : synthesize? cfg (blocks.filter (· ≠ target .right)) number number_injective = none :=
  by cbv

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Regression
