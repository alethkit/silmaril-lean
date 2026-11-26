module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Regression

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Frame Terminator)
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
private abbrev entrySigs : List (List (Diamond.Ty Width)) := [[byte], [byte]]
private abbrev headerSigs : List (List (Diamond.Ty Width)) := [[byte], [pred], [byte]]

-- Initialize the latch to start + 1. The first header binding doubles the
-- captured stride, or uses the latch in the deliberately rejected variant.
-- Feedback adds this binding to the latch. The exit edge returns the binding.
private def loop (dependent : Bool) : Program Input i8 i8 entrySigs headerSigs where
  preheader :=
    .cons (.arithmetic (.constant (1 : BitVec 8))) .nil
      (.cons (.arithmetic (.binary .addi))
        (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (if dependent then .tail (.tail (.tail .head)) else .tail (.tail .head)))
        (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.ult i8)
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
        (.cons (.arithmetic (.binary .addi))
          (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.output (0 : Fin 2) .head) .nil))
          .nil))
  phiInputs
    | .entry => .cons (.output (1 : Fin 2) .head) .nil
    | .backedge => .cons (.output (2 : Fin 3) .head) .nil
  predicate := .output (1 : Fin 3) .head
  result := .output (0 : Fin 3) .head

private abbrev BeforeLabel := SourceLabel i8 i8
private def stage : BlockId BeforeLabel → Nat
  | none => 0
  | some ⟨_, .header⟩ => 1
  | some ⟨_, .exit⟩ => 2

private theorem stage_injective {a b : BlockId BeforeLabel} (same : stage a = stage b) : a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [stage] at same
  · cases a <;> simp [stage] at same
  · cases a <;> cases b <;> simp_all [stage]

private theorem edge_bound {dependent : Bool} {src : BlockId BeforeLabel} {dst : Target BeforeLabel}
    (slot : EdgeSlot) (edge : (shape (lower (loop dependent)) src).target slot = some dst) :
    stage (some dst) ≤ stage src + 1 := by
  cases dependent <;>
    (rcases src with _ | ⟨_, label⟩
     · cases slot <;> cases edge <;> decide
     · cases label <;> cases slot <;> cases edge <;> decide)

private theorem path_visits {dependent : Bool} {a b : BlockId BeforeLabel} {past}
    (path : EntryPath (lower (loop dependent)) b past) (ancestor : stage a ≤ stage b) :
    a ∈ past := by
  induction path with
  | entry => exact List.mem_singleton.mpr (stage_injective (Nat.eq_zero_of_le_zero ancestor))
  | @step src prior dst previous slot edge ih =>
    by_cases same : stage a = stage (some dst)
    · exact List.mem_cons.mpr (.inl (stage_injective same))
    · have bound := edge_bound slot edge
      exact List.mem_cons_of_mem _ (ih (by omega))

private theorem reachable (dependent : Bool) (b : BlockId BeforeLabel) :
    Reachable (lower (loop dependent)) b := by
  have reachesHeader : EntryPath (lower (loop dependent)) headerId [headerId, none] := by
    cases dependent <;> exact .step .entry .jump rfl
  rcases b with _ | ⟨_, label⟩
  · exact ⟨_, .entry⟩
  cases label
  · exact ⟨_, reachesHeader⟩
  · cases dependent <;> exact ⟨_, .step reachesHeader .onFalse rfl⟩

private def tree (dependent : Bool) : DominatorTree (lower (loop dependent)) where
  address := fun b => List.replicate (stage b) 0
  entry_address := rfl
  address_injective := fun h => stage_injective (by simpa using congrArg List.length h)
  reachable := fun _ => true
  reachable_sound := fun {b} _ => reachable dependent b
  prefix_sound := fun _ ancestor _ path =>
    path_visits path (by simpa [List.prefix_replicate_iff] using ancestor)

private def captured : Operands Input [i8, i8] :=
  .cons (.there (.there .here)) (.cons (.there (.there .here)) .nil)

private def rest : Block TargetOp BeforeLabel (i8 :: i8 :: Input) [i8] :=
  .letOp (.ult i8) (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))
    (.letOp (.original (.binary i8 .addi))
      (.cons (.there (.there .here)) (.cons (.there .here) .nil))
      (.terminator (.condBr (.there .here)
        ⟨.header, .cons .here .nil⟩ ⟨.exit, .cons (.there (.there .here)) .nil⟩)))

private def moved : Output Input i8 i8 :=
  ⟨i8, emit (lower (loop false)).entry (.original (.binary i8 .addi)) captured rest⟩

private theorem selected : pickAndHoist? (loop false) (tree false) = some (⟨none, 0⟩, moved) := by cbv

example : (LoopForest.forest? (tree false) blocks).map (fun loops =>
    (LoopForest.depth (tree false) loops none, LoopForest.depth (tree false) loops headerId)) =
    some (0, 1) := by cbv

example : (shape (lower (loop false)) none).bindings = 2 := rfl
example : (shape moved.2 none).bindings = 3 := rfl
example : (shape (lower (loop false)) headerId).bindings = 3 := rfl
example : (shape moved.2 (some ⟨_, .header⟩)).bindings = 2 := rfl

example : useSites 0 1 rest = [.ordinary ⟨headerId, 2⟩, .phi headerId .onFalse 0] := rfl

private def latchDependent : Operands (i8 :: Input) [i8, i8] :=
  .cons .here (.cons (.there (.there (.there .here))) .nil)

example : (lower (loop true)).block .header =
    .letOp (.original (.binary i8 .addi)) latchDependent rest := rfl

example : checkPlacement (tree true) (operandSites latchDependent) (useSites 0 1 rest)
    ⟨none, 0⟩ = false := by cbv

example : LoopForest.choosePlacement (tree true) blocks (operandSites latchDependent) (useSites 0 1 rest) =
    some ⟨headerId, 0⟩ := by cbv

example : capture? latchDependent = none := rfl
example : pickAndHoist? (loop true) (tree true) = none := by cbv

private def input (start limit stride : BitVec 8) : Env Input :=
  .cons start (.cons limit (.cons stride .nil))

private def many := input 2 7 1
private def zero := input 8 7 3

-- Entry retains its existing initialization. Two feedback edges carry
-- the same saved value while advancing the old latch from 3 to 5 to 7.
example : moved.2.entry.eval evalOp (fun term vals => term.eval vals) many =
    .inl (⟨.header, .cons 2 (.cons 3 .nil)⟩ : Frame (Label i8 i8 i8)) := rfl
example : (moved.2.block .header).eval evalOp (fun term vals => term.eval vals)
    (.cons 2 (.cons 3 many)) =
    .inl (⟨.header, .cons 2 (.cons 5 .nil)⟩ : Frame (Label i8 i8 i8)) := rfl
example : (moved.2.block .header).eval evalOp (fun term vals => term.eval vals)
    (.cons 2 (.cons 5 many)) =
    .inl (⟨.header, .cons 2 (.cons 7 .nil)⟩ : Frame (Label i8 i8 i8)) := rfl

example : (lower (loop false)).run evalOp 3 zero = some (.cons 6 .nil) := rfl
example : moved.2.run evalOp 3 zero = some (.cons 6 .nil) := rfl
example : (lower (loop false)).run evalOp 5 many = some (.cons 2 .nil) := rfl
example : moved.2.run evalOp 5 many = some (.cons 2 .nil) := rfl
example : moved.2.run evalOp 4 many = none := rfl

example (budget : Nat) :
    moved.2.run evalOp (budget + 3) many =
      ((loop false).evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs many)).map
        (fun value => Env.cons value .nil) :=
  pickAndHoist?_budget selected many budget

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Regression
