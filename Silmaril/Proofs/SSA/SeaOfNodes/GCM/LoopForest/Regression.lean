module

import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopForest
open Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop (Backedge)

attribute [local cbv_eval] List.minOn?_nil List.minOn?_cons
  List.maxOn?_nil List.maxOn?_cons minOn_eq_ite maxOn_eq_ite

private inductive Label : List Width → Type
  | preheader : Label [i1]
  | header : Label [i1]
  | left : Label [i1]
  | right : Label [i1]
  | exit : Label [i1]

private def cfg : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.br ⟨.preheader, .cons .here .nil⟩)
  block
    | .preheader => .letOp (w := i1) () .nil (.terminator (.condBr (.there .here)
        ⟨.header, .cons .here .nil⟩ ⟨.exit, .cons .here .nil⟩))
    | .header => .terminator (.condBr .here ⟨.left, .cons .here .nil⟩ ⟨.right, .cons .here .nil⟩)
    | .left => .terminator (.condBr .here ⟨.header, .cons .here .nil⟩ ⟨.left, .cons .here .nil⟩)
    | .right => .terminator (.condBr .here ⟨.header, .cons .here .nil⟩ ⟨.header, .cons .here .nil⟩)
    | .exit => .terminator (.ret (.cons .here .nil))

private def preheader : Target Label := ⟨_, .preheader⟩
private def header : Target Label := ⟨_, .header⟩
private def left : Target Label := ⟨_, .left⟩
private def right : Target Label := ⟨_, .right⟩
private def exit : Target Label := ⟨_, .exit⟩

private def address : BlockId Label → List Nat
  | none => []
  | some ⟨_, .preheader⟩ => [0]
  | some ⟨_, .header⟩ => [0, 0]
  | some ⟨_, .left⟩ => [0, 0, 0]
  | some ⟨_, .right⟩ => [0, 0, 1]
  | some ⟨_, .exit⟩ => [0, 1]

private theorem address_injective {a b : BlockId Label} (same : address a = address b) : a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [address] at same
  · cases a <;> simp [address] at same
  · cases a <;> cases b <;> simp_all [address]

-- An ancestor of the destination either is that destination or was
-- already an ancestor of the source, including on the backward edges.
private theorem ancestor_step (a : BlockId Label) {src : BlockId Label} {dst : Target Label}
    (slot : EdgeSlot) (actual : (shape cfg src).target slot = some dst)
    (ancestor : (address a).isPrefixOf (address (some dst)) = true) :
    address a = address (some dst) ∨ (address a).isPrefixOf (address src) = true := by
  rcases src with _ | ⟨_, label⟩
  · cases slot <;> cases actual
    rcases a with _ | ⟨_, label⟩
    · exact .inr rfl
    · cases label <;> first | exact .inl rfl | cases ancestor
  · cases label <;> cases slot <;> cases actual <;>
      (rcases a with _ | ⟨_, label⟩
       · exact .inr rfl
       · cases label <;> first | exact .inl rfl | exact .inr rfl | cases ancestor)

private theorem path_visits {a b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) (ancestor : (address a).isPrefixOf (address b) = true) :
    a ∈ past := by
  induction path with
  | entry =>
    rcases a with _ | ⟨_, label⟩
    · exact List.mem_cons_self
    · cases label <;> cases ancestor
  | @step src prior dst previous slot actual ih =>
    rcases ancestor_step a slot actual ancestor with same | above
    · exact List.mem_cons.mpr (.inl (address_injective same))
    · exact List.mem_cons_of_mem _ (ih above)

private def trail : BlockId Label → List (BlockId Label)
  | none => [none]
  | some ⟨_, .preheader⟩ => [some preheader, none]
  | some ⟨_, .header⟩ => [some header, some preheader, none]
  | some ⟨_, .left⟩ => [some left, some header, some preheader, none]
  | some ⟨_, .right⟩ => [some right, some header, some preheader, none]
  | some ⟨_, .exit⟩ => [some exit, some preheader, none]

private theorem trail_path (b : BlockId Label) : EntryPath cfg b (trail b) := by
  have toPreheader : EntryPath cfg (some preheader) (trail (some preheader)) := .step .entry .jump rfl
  have toHeader : EntryPath cfg (some header) (trail (some header)) := .step toPreheader .onTrue rfl
  rcases b with _ | ⟨_, label⟩
  · exact .entry
  cases label
  · exact toPreheader
  · exact toHeader
  · exact .step toHeader .onTrue rfl
  · exact .step toHeader .onFalse rfl
  · exact .step toPreheader .onFalse rfl

private def tree : DominatorTree cfg where
  address := address
  entry_address := rfl
  address_injective := address_injective
  reachable := fun _ => true
  reachable_sound := fun {b} _ => ⟨trail b, trail_path b⟩
  prefix_sound := fun _ ancestor _ path => path_visits path (List.isPrefixOf_iff_prefix.mpr ancestor)

private theorem trail_prefix {a b : BlockId Label} (visited : a ∈ trail b) :
    (address a).isPrefixOf (address b) = true := by
  rcases a with _ | ⟨_, a⟩
  · rfl
  rcases b with _ | ⟨_, b⟩
  · cases a <;> simp [trail] at visited
  · cases a <;> cases b <;>
      first | rfl | simp [trail, preheader, header, left, right, exit] at visited

private theorem complete : tree.Complete where
  reachable_complete := fun _ => rfl
  prefix_complete := fun {_ b} _ dominates => List.isPrefixOf_iff_prefix.mp
    (trail_prefix (dominates (trail b) (trail_path b)))

-- Duplicating the right block in the inventory does not multiply its slots.
private def blocks : List (Target Label) := [right, left, header, preheader, exit, right]
private def edges : List (Backedge Label) :=
  [⟨header, right, .onTrue⟩, ⟨header, right, .onFalse⟩, ⟨header, left, .onTrue⟩, ⟨left, left, .onFalse⟩]

private theorem discovers : discover? tree blocks = some edges := by cbv

example (edge : Backedge Label) : edge ∈ edges ↔ ActualBackedge cfg edge :=
  mem_discover_iff discovers complete edge
example : discover? tree [right, header, preheader, exit] = none := by cbv

private def loops : List (HeaderLoop Label) :=
  [⟨header, [some header, some right, some left]⟩, ⟨left, [some left]⟩]

example : forest? tree blocks = some loops := by cbv

-- The parallel occurrences and two latches contribute only one outer
-- loop. The left latch also belongs to the strictly nested self-loop.
example : (blocks.map fun b => depth tree loops (some b)) = [1, 2, 1, 0, 0, 1] := by cbv

-- The admission test rejects intersecting sets when neither contains the other.
example : checkLaminar tree
    [⟨header, [some header, some right]⟩, ⟨left, [some left, some right]⟩] = false := by cbv

private def operand : Point Label := ⟨some preheader, 1⟩
private def phiUses : List (Use Label) := [.phi (some right) .onTrue 0, .phi (some right) .onFalse 0]

example : discoverPlacement tree blocks [operand] phiUses = some ⟨some right, 0⟩ := by cbv
example : choosePlacement tree blocks [operand] phiUses = some operand := by cbv

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.Regression
