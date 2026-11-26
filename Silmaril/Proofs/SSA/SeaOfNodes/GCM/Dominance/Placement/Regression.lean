module

import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement

private inductive Label : List Width → Type
  | left : Label [i1]
  | right : Label [i1]
  | join : Label [i1]
  deriving DecidableEq

private def diamond : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .letOp (w := i1) () .nil (.terminator
    (.condBr .here ⟨.left, .cons .here .nil⟩ ⟨.right, .cons .here .nil⟩))
  block
    | .left => .letOp (w := i1) () .nil (.terminator
      (.condBr .here ⟨.join, .cons .here .nil⟩ ⟨.join, .cons (.there .here) .nil⟩))
    | .right => .terminator (.br ⟨.join, .cons .here .nil⟩)
    | .join => .terminator (.ret (.cons .here .nil))

private def blocks : List (Target Label) := [⟨_, .join⟩, ⟨_, .right⟩, ⟨_, .left⟩]
private def entryCut : Point Label := ⟨none, 1⟩
private def leftCut : Point Label := ⟨some ⟨_, .left⟩, 1⟩
private def rightCut : Point Label := ⟨some ⟨_, .right⟩, 0⟩
private def joinRead : Use Label := .ordinary ⟨some ⟨_, .join⟩, 0⟩
private def phiReads : List (Use Label) :=
  [.phi (some ⟨_, .left⟩) .onTrue 0, .phi (some ⟨_, .left⟩) .onFalse 0]

-- Both parallel occurrences read at the left terminator after the local binding.
example : discoverCut diamond blocks [leftCut] phiReads = some leftCut := by cbv
example : checkCut diamond blocks [leftCut] phiReads ⟨leftCut.block, 0⟩ = false := by cbv
example : checkCut diamond blocks [leftCut] [.phi leftCut.block .jump 0] leftCut = false := by cbv

-- A join use also needs coverage of the path through the right arm.
example : discoverCut diamond blocks [entryCut] (joinRead :: phiReads) = some entryCut := by cbv
example : discoverCut diamond blocks [leftCut] (joinRead :: phiReads) = none := by cbv
example : discoverCut diamond blocks [rightCut] phiReads = none := by cbv

-- Omitting the right arm fails the successor-closure guard even for empty constraints.
example : discoverCut diamond [⟨_, .join⟩, ⟨_, .left⟩] [] [] = none := by cbv

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement.Regression
