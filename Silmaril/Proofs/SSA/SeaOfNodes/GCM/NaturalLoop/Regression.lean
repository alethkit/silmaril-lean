module

import Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop

attribute [local cbv_eval] reverseClose.eq_1 List.minOn?_nil List.minOn?_cons
  List.maxOn?_nil List.maxOn?_cons minOn_eq_ite maxOn_eq_ite

private inductive Label : List Width → Type
  | preheader : Label [i1]
  | header : Label [i1]
  | body : Label [i1]
  | latch : Label [i1]
  | exit : Label [i1]

private def cfg : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.br ⟨.preheader, .cons .here .nil⟩)
  block
    | .preheader => .letOp (w := i1) () .nil (.terminator (.br ⟨.header, .cons .here .nil⟩))
    | .header => .terminator (.br ⟨.body, .cons .here .nil⟩)
    | .body => .terminator (.br ⟨.latch, .cons .here .nil⟩)
    | .latch => .terminator (.condBr .here ⟨.header, .cons .here .nil⟩
        ⟨.exit, .cons .here .nil⟩)
    | .exit => .terminator (.ret (.cons .here .nil))

private def preheader : Target Label := ⟨_, .preheader⟩
private def header : Target Label := ⟨_, .header⟩
private def body : Target Label := ⟨_, .body⟩
private def latch : Target Label := ⟨_, .latch⟩
private def exit : Target Label := ⟨_, .exit⟩

private def stage : BlockId Label → Nat
  | none => 0
  | some ⟨_, .preheader⟩ => 1
  | some ⟨_, .header⟩ => 2
  | some ⟨_, .body⟩ => 3
  | some ⟨_, .latch⟩ => 4
  | some ⟨_, .exit⟩ => 5

private theorem stage_injective {a b : BlockId Label} (same : stage a = stage b) : a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [stage] at same
  · cases a <;> simp [stage] at same
  · cases a <;> cases b <;> simp_all [stage]

-- The backedge decreases the stage. No occurrence increases it by more than one.
private theorem edge_bound {src : BlockId Label} {dst : Target Label} (slot : EdgeSlot)
    (actual : (shape cfg src).target slot = some dst) :
    stage (some dst) ≤ stage src + 1 := by
  rcases src with _ | ⟨_, label⟩
  · cases slot <;> cases actual <;> decide
  · cases label <;> cases slot <;> cases actual <;> decide

private theorem path_visits {a b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) (before : stage a ≤ stage b) : a ∈ past := by
  induction path with
  | entry =>
    exact List.mem_singleton.mpr (stage_injective (Nat.eq_zero_of_le_zero before))
  | @step src prior dst previous slot actual ih =>
    by_cases same : stage a = stage (some dst)
    · exact List.mem_cons.mpr (.inl (stage_injective same))
    · have bound := edge_bound slot actual
      exact List.mem_cons_of_mem _ (ih (by omega))

private theorem preheader_path : EntryPath cfg (some preheader) [some preheader, none] :=
  .step .entry .jump rfl
private theorem header_path :
    EntryPath cfg (some header) [some header, some preheader, none] :=
  .step preheader_path .jump rfl
private theorem body_path :
    EntryPath cfg (some body) [some body, some header, some preheader, none] :=
  .step header_path .jump rfl
private theorem latch_path :
    EntryPath cfg (some latch) [some latch, some body, some header, some preheader, none] :=
  .step body_path .jump rfl
private theorem exit_path :
    EntryPath cfg (some exit) [some exit, some latch, some body, some header, some preheader, none] :=
  .step latch_path .onFalse rfl

private theorem reachable (b : BlockId Label) : Reachable cfg b := by
  rcases b with _ | ⟨_, label⟩
  · exact ⟨[none], .entry⟩
  cases label
  · exact ⟨_, preheader_path⟩
  · exact ⟨_, header_path⟩
  · exact ⟨_, body_path⟩
  · exact ⟨_, latch_path⟩
  · exact ⟨_, exit_path⟩

private def tree : DominatorTree cfg where
  address := fun b => List.replicate (stage b) 0
  entry_address := rfl
  address_injective := fun h => stage_injective (by simpa using congrArg List.length h)
  reachable := fun _ => true
  reachable_sound := fun {b} _ => reachable b
  prefix_sound := fun _ ancestor _ path => path_visits path (by
    simpa [List.prefix_replicate_iff] using ancestor)

private def blocks : List (Target Label) := [exit, latch, body, header, preheader]
private def edge : Backedge Label := ⟨header, latch, .onTrue⟩
private def loopMembers : List (BlockId Label) := [some header, some body, some latch]

-- The traversal starts at the latch and discovers the body. It stops at the
-- header before reaching the preheader.
example : checkedMembers? tree blocks edge = some loopMembers := by cbv

example : (blocks.map fun b => depth tree loopMembers (some b)) = [0, 1, 1, 1, 0] := by cbv

-- The preheader jump is real, but its destination does not dominate its source.
example : checkedMembers? tree blocks ⟨header, preheader, .jump⟩ = none := by cbv

-- The same latch has no unconditional jump occurrence.
example : checkedMembers? tree blocks {edge with slot := .jump} = none := by cbv

-- A different, existing occurrence at the latch targets the exit.
example : checkedMembers? tree blocks {edge with slot := .onFalse} = none := by cbv

-- Omitting the reachable body breaks successor closure.
example : checkedMembers? tree [exit, latch, header, preheader] edge = none := by cbv

private def operand : Point Label := ⟨some preheader, 1⟩
private def phi : Use Label := .phi (some latch) .onFalse 0

example : phi.point? cfg = some ⟨some latch, 0⟩ := rfl

example : discoverPlacement tree blocks [operand] [phi] = some ⟨some latch, 0⟩ := by cbv

example : choosePlacement tree blocks edge [operand] [phi] = some operand := by cbv

example : choosePlacement tree blocks {edge with slot := .jump} [operand] [phi] = none := by cbv

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.Regression
