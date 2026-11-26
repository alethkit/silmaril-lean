module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Regression

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

attribute [local cbv_eval] List.minOn?_nil List.minOn?_cons List.maxOn?_nil List.maxOn?_cons
  minOn_eq_ite maxOn_eq_ite

private def i8 : Width := ⟨8, by decide⟩
private abbrev byte : Diamond.Ty Width := .value (.data i8)
private abbrev pred : Diamond.Ty Width := .value .predicate
private abbrev Input := [i8, i8, i8]
private abbrev BeforeLabel := SourceLabel i8 i8

-- The first binding feeds both the backedge and exit. It is either twice
-- the captured stride or the current latch plus the stride.
private def loop (dependent : Bool) : Program Input i8 i8 [] [[byte], [pred]] where
  preheader := .nil
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (if dependent then .tail (.tail (.tail .head)) else .tail (.tail .head)))
        (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.ult i8)
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
        .nil)
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (0 : Fin 2) .head) .nil
  predicate := .output (1 : Fin 2) .head
  result := .output (0 : Fin 2) .head

private def header : Target BeforeLabel := ⟨_, .header⟩
private def exit : Target BeforeLabel := ⟨_, .exit⟩
private def computed := Dominance.certificate (loop false)

example : (computed.address none, computed.address (some header), computed.address (some exit)) =
    ([], [0], [0, 0]) := rfl
example : computed.Complete := Dominance.certificate_complete (loop false)
example : NaturalLoop.checkInventory computed blocks = true := by cbv
example : NaturalLoop.checkInventory computed [header] = false := by cbv
example : LoopForest.discover? computed blocks = some [⟨header, header, .onTrue⟩] := by cbv

example : (shape (lower (loop false)) (some header)).target .onTrue = some header := rfl
example : (shape (lower (loop false)) (some header)).target .onFalse = some exit := rfl
example : (Use.phi (some header) .onTrue 0).point? (lower (loop false)) = some ⟨some header, 2⟩ := rfl
example : (Use.phi (some header) .onFalse 0).point? (lower (loop false)) = some ⟨some header, 2⟩ := rfl
example : (Use.phi (some header) .jump 0).point? (lower (loop false)) = none := rfl
example : checkPlacement computed [⟨none, 0⟩] [.phi (some header) .jump 0] ⟨none, 0⟩ = false := by cbv

private def rest : Block TargetOp BeforeLabel (i8 :: i8 :: Input) [i8] :=
  .letOp (.ult i8) (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))
    (.terminator (.condBr .here ⟨.header, .cons (.there .here) .nil⟩
      ⟨.exit, .cons (.there .here) .nil⟩))

example : useSites 0 1 rest = [.phi (some header) .onTrue 0, .phi (some header) .onFalse 0] := rfl

private def captured : Operands Input [i8, i8] :=
  .cons (.there (.there .here)) (.cons (.there (.there .here)) .nil)

private def moved : Output Input i8 i8 :=
  ⟨i8, emit (lower (loop false)).entry (.original (.binary i8 .addi)) captured rest⟩

private theorem picked : Dominance.pickAndHoist? (loop false) = some (⟨none, 0⟩, moved) := by cbv
example : Dominance.pickAndHoist? (loop true) = none := by cbv

private def input : Env Input := .cons 1 (.cons 4 (.cons 3 .nil))

example : moved.2.run evalOp 3 input = none := rfl
example : moved.2.run evalOp 4 input = some (.cons 6 .nil) := rfl

example (budget : Nat) :
    moved.2.run evalOp (budget + 3) input =
      ((loop false).evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Dominance.pickAndHoist?_budget picked input budget

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Regression
