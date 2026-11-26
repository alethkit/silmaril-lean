module

import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature i1)
open Silmaril.SSA.SeaOfNodes.GCM

private inductive Label : List Width → Type
  | work : Label [i1]
  | merge : Label [i1]

private inductive Op : OpSignature
  | seed : Op [] i1
  | consume : Op [i1] i1

/-- Both arms enter the same join and pass different register operands.
The middle block has two bindings before its conditional terminator. -/
private def cfg : Cfg Op Label [i1] [i1] where
  entry := .terminator (.br ⟨.work, .cons .here .nil⟩)
  block
    | .work => .letOp .seed .nil
      (.letOp .consume (.cons .here .nil)
        (.terminator (.condBr (.there (.there .here))
          ⟨.merge, .cons .here .nil⟩ ⟨.merge, .cons (.there .here) .nil⟩)))
    | .merge => .terminator (.ret (.cons .here .nil))

private def workTarget : Target Label := ⟨_, .work⟩
private def mergeTarget : Target Label := ⟨_, .merge⟩
private def work : BlockId Label := some workTarget
private def merge : BlockId Label := some mergeTarget

private def address : BlockId Label → List Nat
  | none => []
  | some ⟨_, .work⟩ => [0]
  | some ⟨_, .merge⟩ => [0, 0]

private theorem address_injective {a b : BlockId Label} (eq : address a = address b) : a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [address] at eq
  · cases a <;> simp [address] at eq
  · cases a <;> cases b <;> simp_all [address]

private theorem entry_mem {b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) : none ∈ past := by
  induction path with
  | entry => simp
  | step _ _ _ ih => exact List.mem_cons_of_mem _ ih

private theorem endpoint_mem {b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) : b ∈ past := by
  cases path <;> exact List.mem_cons_self

private theorem work_path : EntryPath cfg work [work, none] := .step .entry .jump rfl
private theorem merge_path : EntryPath cfg merge [merge, work, none] := .step work_path .onTrue rfl

private theorem work_mem {past : List (BlockId Label)} (path : EntryPath cfg merge past) :
    work ∈ past := by
  cases path with
  | @step src prior dst previous slot edge =>
    have source : src = work := by
      rcases src with _ | ⟨_, label⟩
      · cases slot <;> cases edge
      cases label
      · rfl
      · cases slot <;> cases edge
    exact List.mem_cons_of_mem _ (source ▸ endpoint_mem previous)

private theorem reachable (b : BlockId Label) : Reachable cfg b := by
  rcases b with _ | ⟨_, label⟩
  · exact ⟨[none], .entry⟩
  cases label
  · exact ⟨_, work_path⟩
  · exact ⟨_, merge_path⟩

private theorem prefix_sound {a b : BlockId Label}
    (ancestry : List.IsPrefix (address a) (address b)) : Dominates cfg a b := by
  intro past path
  rcases a with _ | ⟨_, a⟩
  · exact entry_mem path
  rcases b with _ | ⟨_, b⟩
  · cases a <;> simp [address] at ancestry
  cases a <;> cases b
  · exact endpoint_mem path
  · exact work_mem path
  · simp [address, List.cons_prefix_iff] at ancestry
  · exact endpoint_mem path

private def tree : DominatorTree cfg where
  address := address
  entry_address := rfl
  address_injective := address_injective
  reachable := fun _ => true
  reachable_sound := fun {b} _ => reachable b
  prefix_sound := fun _ h => prefix_sound h

private theorem complete : tree.Complete := by
  refine ⟨fun _ => rfl, ?_⟩
  intro a b _ dominates
  rcases b with _ | ⟨_, label⟩
  · have same : a = none := List.mem_singleton.mp (dominates [none] .entry)
    subst a
    decide
  cases label
  · have visited := dominates _ work_path
    simp only [List.mem_cons, List.not_mem_nil, or_false] at visited
    rcases visited with rfl | rfl <;> decide
  · have visited := dominates _ merge_path
    simp only [List.mem_cons, List.not_mem_nil, or_false] at visited
    rcases visited with rfl | rfl | rfl <;> decide

-- Merge precedes work in the search order. It cannot supply an incoming read at work.
private def blocks : List (Target Label) := [mergeTarget, workTarget]
private def middle : Point Label := ⟨work, 1⟩
private def final : Point Label := ⟨work, 2⟩
private def truePhi : Use Label := .phi work .onTrue 0
private def falsePhi : Use Label := .phi work .onFalse 0
private def uses : List (Use Label) := [.ordinary middle, truePhi, falsePhi]

example : truePhi.point? cfg = some final := rfl
example : falsePhi.point? cfg = some final := rfl

-- Insertion follows the first binding and precedes the second binding's read.
example : discoverPlacement tree blocks [middle] uses = some middle := rfl
example : discoverPlacement tree blocks [middle] [truePhi, falsePhi] = some middle := rfl

example : Legal cfg [middle] uses middle :=
  checkPlacement_sound tree (discoverPlacement_sound tree blocks (operands := [middle])
    (uses := uses) (candidate := middle) rfl).2

-- Omitting work from the inventory omits its otherwise legal cut.
example : discoverPlacement tree [mergeTarget] [middle] uses = none := rfl

-- The operand at cut 2 is too late for the ordinary use at cut 1.
example : discoverPlacement tree blocks [final] uses = none := rfl

example : ∀ p ∈ candidateCuts cfg blocks, ¬ Legal cfg [final] uses p :=
  (discoverPlacement_eq_none_iff_no_legal tree complete blocks [final] uses).mp rfl

-- Resolve each occurrence and argument before considering the position.
example : discoverPlacement tree blocks [middle] (uses ++ [.phi work .jump 0]) = none := rfl
example : discoverPlacement tree blocks [middle] (uses ++ [.phi work .onFalse 1]) = none := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.Regression
