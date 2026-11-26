module

import Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM

attribute [local cbv_eval] List.minOn?_nil List.minOn?_cons List.maxOn?_nil List.maxOn?_cons
  minOn_eq_ite maxOn_eq_ite

private inductive Label : List Width → Type
  | preheader : Label [i1]
  | header : Label [i1]
  | exit : Label [i1]

/-- The true arm at the loop header is a backedge to itself. The false
arm passes the previously bound block argument to the exit. -/
private def cfg : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.br ⟨.preheader, .cons .here .nil⟩)
  block
    | .preheader => .letOp (w := i1) () .nil (.terminator (.br ⟨.header, .cons .here .nil⟩))
    | .header => .letOp (w := i1) () .nil (.terminator (.condBr (.there .here)
        ⟨.header, .cons .here .nil⟩ ⟨.exit, .cons (.there .here) .nil⟩))
    | .exit => .terminator (.ret (.cons .here .nil))

private def preheaderTarget : Target Label := ⟨_, .preheader⟩
private def headerTarget : Target Label := ⟨_, .header⟩
private def exitTarget : Target Label := ⟨_, .exit⟩
private def preheader : BlockId Label := some preheaderTarget
private def header : BlockId Label := some headerTarget
private def exit : BlockId Label := some exitTarget

-- In this fixture every edge stays at the same stage or advances by one.
private def stage : BlockId Label → Nat
  | none => 0
  | some ⟨_, .preheader⟩ => 1
  | some ⟨_, .header⟩ => 2
  | some ⟨_, .exit⟩ => 3

private theorem stage_injective {a b : BlockId Label} (same : stage a = stage b) : a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [stage] at same
  · cases a <;> simp [stage] at same
  · cases a <;> cases b <;> simp_all [stage]

private theorem ordered_edge {src : BlockId Label} {dst : Target Label} (slot : EdgeSlot)
    (edge : (shape cfg src).target slot = some dst) :
    stage src ≤ stage (some dst) ∧ stage (some dst) ≤ stage src + 1 := by
  rcases src with _ | ⟨_, label⟩
  · cases slot <;> cases edge <;> decide
  · cases label <;> cases slot <;> cases edge <;> decide

private theorem path_visits {a b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) : a ∈ past ↔ stage a ≤ stage b := by
  induction path with
  | entry =>
    constructor
    · intro member
      simpa only [List.mem_singleton.mp member] using Nat.le_refl (stage none)
    · intro bound
      exact List.mem_singleton.mpr (stage_injective (Nat.eq_zero_of_le_zero bound))
  | @step src prior dst previous slot edge ih =>
    have order := ordered_edge slot edge
    constructor
    · intro member
      rcases List.mem_cons.mp member with same | earlier
      · exact same.symm ▸ Nat.le_refl _
      · exact Nat.le_trans (ih.mp earlier) order.1
    · intro bound
      by_cases same : stage a = stage (some dst)
      · exact List.mem_cons.mpr (.inl (stage_injective same))
      · exact List.mem_cons_of_mem _ (ih.mpr (by omega))

private def address (b : BlockId Label) : List Nat := List.replicate (stage b) 0

private theorem address_prefix {a b : BlockId Label} :
    List.IsPrefix (address a) (address b) ↔ stage a ≤ stage b := by
  simp [address, List.prefix_replicate_iff]

private theorem preheader_path : EntryPath cfg preheader [preheader, none] := .step .entry .jump rfl
private theorem header_path : EntryPath cfg header [header, preheader, none] :=
  .step preheader_path .jump rfl
private theorem exit_path : EntryPath cfg exit [exit, header, preheader, none] :=
  .step header_path .onFalse rfl

private theorem reachable (b : BlockId Label) : Reachable cfg b := by
  rcases b with _ | ⟨_, label⟩
  · exact ⟨[none], .entry⟩
  cases label
  · exact ⟨_, preheader_path⟩
  · exact ⟨_, header_path⟩
  · exact ⟨_, exit_path⟩

private def tree : DominatorTree cfg where
  address := address
  entry_address := rfl
  address_injective := fun h => stage_injective (by simpa [address] using congrArg List.length h)
  reachable := fun _ => true
  reachable_sound := fun {b} _ => reachable b
  prefix_sound := fun _ ancestor _ path => (path_visits path).mpr (address_prefix.mp ancestor)

private theorem complete : tree.Complete where
  reachable_complete := fun _ => rfl
  prefix_complete := by
    rintro a b ⟨past, path⟩ dominates
    exact address_prefix.mpr ((path_visits path).mp (dominates past path))

-- Supply depth one at the self-loop header and zero elsewhere.
private def loopDepth : BlockId Label → Nat
  | some ⟨_, .header⟩ => 1
  | _ => 0

example : (shape cfg header).target .onTrue = some headerTarget := rfl

private def blocks : List (Target Label) := [exitTarget, headerTarget, preheaderTarget]
private def operand : Point Label := ⟨preheader, 1⟩
private def exitStart : Point Label := ⟨exit, 0⟩
private def phi : Use Label := .phi header .onFalse 0

example : phi.point? cfg = some ⟨header, 1⟩ := rfl
example : discoverPlacement tree blocks [operand] [phi] = some ⟨header, 0⟩ := rfl
example : chooseLoopPlacement tree loopDepth blocks [operand] [phi] = some operand := by cbv

-- The earlier-enumerated exit has depth zero and a longer dominator address.
-- It wins for an ordinary read there, but the Phi's real read is on the edge.
example : chooseLoopPlacement tree loopDepth blocks [operand] [.ordinary exitStart] =
    some exitStart := by cbv
example : checkPlacement tree [operand] [phi] exitStart = false := rfl

-- Both entry and preheader have depth zero. The preheader has the deeper
-- address, and its two cuts tie, so the first cut is selected.
example : chooseLoopPlacement tree loopDepth blocks [⟨none, 0⟩] [phi] =
    some ⟨preheader, 0⟩ := by cbv

example : ∀ cut ∈ candidateCuts cfg blocks, ¬ Legal cfg [operand] [.phi header .jump 0] cut :=
  (chooseLoopPlacement_complete tree loopDepth blocks [operand] [.phi header .jump 0] complete).mp (by cbv)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.Regression
