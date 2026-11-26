module

import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance

private inductive Label : List Width → Type
  | left : Label [i1]
  | right : Label [i1]
  | join : Label [i1]
  | header : Label [i1]
  | latch : Label [i1]
  | exit : Label [i1]
  | dead : Label []
  deriving DecidableEq

private def target {args : List Width} (label : Label args) : Target Label := ⟨args, label⟩
private def block {args : List Width} (label : Label args) : BlockId Label := some (target label)

private def diamond : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.condBr .here ⟨.left, .cons .here .nil⟩ ⟨.right, .cons .here .nil⟩)
  block
    | .left | .right => .terminator (.br ⟨.join, .cons .here .nil⟩)
    | .join | .header | .latch | .exit => .terminator (.ret (.cons .here .nil))
    | .dead => .terminator (.ret (.cons .here .nil))

private def diamondBlocks : List (Target Label) := [.join, .left, .right].map target

example : checkClosed diamond diamondBlocks = true := by cbv
example : dominates? diamond diamondBlocks none (block .join) = true := by cbv
example : dominates? diamond diamondBlocks (block .join) (block .join) = true := by cbv
example : dominates? diamond diamondBlocks (block .left) (block .join) = false := by cbv
example : dominates? diamond diamondBlocks (block .right) (block .join) = false := by cbv
example : dominates? diamond [target .left, target .right] none (block .join) = false := by cbv

private def loop : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.br ⟨.header, .cons .here .nil⟩)
  block
    | .header => .terminator (.condBr .here ⟨.latch, .cons .here .nil⟩ ⟨.exit, .cons .here .nil⟩)
    | .latch => .terminator (.condBr .here ⟨.header, .cons .here .nil⟩
        ⟨.header, .cons (.there .here) .nil⟩)
    | .dead => .terminator (.br ⟨.exit, .cons .here .nil⟩)
    | .left | .right | .join | .exit => .terminator (.ret (.cons .here .nil))

private def loopBlocks : List (Target Label) := [target .dead, target .exit, target .latch, target .header]

example : occurrences loop (block .latch) = [(.onTrue, target .header), (.onFalse, target .header)] :=
  by cbv
example : checkClosed loop loopBlocks = true := by cbv
example : dominates? loop loopBlocks (block .header) (block .latch) = true := by cbv
example : dominates? loop loopBlocks (block .header) (block .exit) = true := by cbv
example : dominates? loop loopBlocks (block .latch) (block .exit) = false := by cbv
example : reachable? loop loopBlocks (block .dead) = false := by cbv
example : dominates? loop loopBlocks none (block .dead) = false := by cbv
example : dominates? loop loopBlocks (block .dead) (block .exit) = false := by cbv

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Regression
