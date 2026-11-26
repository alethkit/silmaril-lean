module

import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance
open Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree

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

private def proposed : BlockId Label → List Nat
  | none => []
  | some ⟨_, .left⟩ => [0]
  | some ⟨_, .right⟩ => [1]
  | some ⟨_, .header⟩ => [2]
  | some ⟨_, .latch⟩ => [2, 0]
  | some ⟨_, .exit⟩ => [2, 1]
  | some ⟨_, .dead⟩ | some ⟨_, .outside⟩ => [2]

private def certificate := certify? cfg blocks proposed number number_injective

example : certificate.isSome = true := by cbv
example : occurrences cfg (block .latch) = [(.onTrue, target .header), (.onFalse, target .header)] :=
  by cbv

-- The loop header is also the diamond join. Neither arm dominates it.
example : certificate.map (fun t => (t.1.address (block .left)).isPrefixOf
    (t.1.address (block .header))) = some false := by cbv
example : certificate.map (fun t => (t.1.address (block .right)).isPrefixOf
    (t.1.address (block .header))) = some false := by cbv
example : certificate.map (fun t => (t.1.address (block .header)).isPrefixOf
    (t.1.address (block .latch))) = some true := by cbv

-- The inventoried dead block and the omitted label stay unreachable. Both
-- proposed addresses would collide with the header without the reserved prefix.
example : certificate.map (fun t => (t.1.reachable (block .dead),
    t.1.reachable (block .outside), t.1.address (block .dead), t.1.address (block .outside))) =
    some (false, false, [0, 6], [0, 7]) := by cbv
example : certificate.map (fun t => (t.1.address (block .dead)).isPrefixOf
    (t.1.address (block .exit))) = some false := by cbv

private def phiReads : List (Use Label) :=
  [.phi (block .latch) .onTrue 0, .phi (block .latch) .onFalse 0]

example : certificate.map (fun t => checkPlacement t.1 [⟨none, 0⟩] phiReads
    ⟨block .header, 0⟩) = some true := by cbv
example : certificate.map (fun t => checkPlacement t.1 [⟨none, 0⟩] phiReads
    ⟨block .left, 0⟩) = some false := by cbv
example : certificate.map (fun t => checkPlacement t.1 [] [] ⟨block .dead, 0⟩) =
    some false := by cbv

-- This proposal has one-step parents but puts the left arm above the join.
private def wrongAncestor : BlockId Label → List Nat
  | some ⟨_, .header⟩ => [0, 2]
  | some ⟨_, .latch⟩ => [0, 2, 0]
  | some ⟨_, .exit⟩ => [0, 2, 1]
  | b => proposed b

example : certify? cfg blocks wrongAncestor number number_injective = none := by cbv

-- Pairwise ancestry is correct, but the exit skips a level of the tree.
private def gap : BlockId Label → List Nat
  | some ⟨_, .exit⟩ => [2, 1, 1]
  | b => proposed b

example : certify? cfg blocks gap number number_injective = none := by cbv
example : certify? cfg (blocks.filter (· ≠ target .right)) proposed number number_injective = none :=
  by cbv

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Regression
