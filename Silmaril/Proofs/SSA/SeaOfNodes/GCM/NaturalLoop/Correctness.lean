module

public import Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}
variable {tree : DominatorTree cfg} {blocks : List (Target Label)} {edge : Backedge Label}

private theorem slot_mem (slot : EdgeSlot) : slot ∈ slots := by
  cases slot <;> decide

theorem mem_vertices_iff_reachable (checked : checkInventory tree blocks = true)
    (b : BlockId Label) : b ∈ vertices blocks ↔ Reachable cfg b := by
  letI := blockDecEq tree
  have inventory := List.all_eq_true.mp checked
  constructor
  · intro member
    exact tree.reachable_sound (Bool.and_eq_true_iff.mp (inventory b member)).1
  · rintro ⟨past, path⟩
    induction path with
    | entry => exact List.mem_cons_self
    | @step src _ dst _ slot actual ih =>
      have closed := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (inventory src ih)).2
      simpa [actual] using closed slot (slot_mem slot)

private theorem backedgeChecks (checked : checkBackedge tree blocks edge = true) :
    checkInventory tree blocks = true ∧
      some edge.header ∈ vertices blocks ∧ some edge.latch ∈ vertices blocks ∧
      (shape cfg (some edge.latch)).target edge.slot = some edge.header ∧
      (tree.address (some edge.header)).isPrefixOf (tree.address (some edge.latch)) = true := by
  simpa [checkBackedge, Bool.and_eq_true, and_assoc] using checked

theorem checkBackedge_sound (checked : checkBackedge tree blocks edge = true) :
    Reachable cfg (some edge.header) ∧ Reachable cfg (some edge.latch) ∧
      (shape cfg (some edge.latch)).target edge.slot = some edge.header ∧
      Dominates cfg (some edge.header) (some edge.latch) := by
  obtain ⟨inventory, header, latch, actual, ancestor⟩ := backedgeChecks checked
  exact ⟨(mem_vertices_iff_reachable inventory _).mp header,
    (mem_vertices_iff_reachable inventory _).mp latch, actual,
    tree.prefix_sound ((mem_vertices_iff_reachable inventory _).mp latch)
      (List.isPrefixOf_iff_prefix.mp ancestor)⟩

private theorem edge_eq_true_iff (src dst : BlockId Label) :
    edge? tree src dst = true ↔
      ∃ target, dst = some target ∧ ∃ slot, (shape cfg src).target slot = some target := by
  cases dst with
  | none => simp [edge?]
  | some target => simp [edge?, List.any_eq_true, slot_mem]

theorem reverseClose_spec {B : Type} [DecidableEq B] (hasEdge : B → B → Bool)
    (Q : B → Prop) (remaining reached : List B)
    (seeds : ∀ b ∈ reached, Q b)
    (step : ∀ src ∈ remaining, ∀ dst, hasEdge src dst = true → Q dst → Q src) :
    let closed := reverseClose hasEdge remaining reached
    (∀ b ∈ reached, b ∈ closed) ∧ (∀ b ∈ closed, Q b) ∧
      (∀ src ∈ remaining, ∀ dst ∈ closed, hasEdge src dst = true → src ∈ closed) := by
  fun_induction reverseClose hasEdge remaining reached with
  | case1 remaining reached absent =>
    exact ⟨fun _ h => h, seeds, fun src hin dst hdst actual =>
      False.elim (List.find?_eq_none.mp absent src hin (List.any_eq_true.mpr ⟨dst, hdst, actual⟩))⟩
  | case2 remaining reached src found ih =>
    have available := List.mem_of_find?_eq_some found
    have reaches : reached.any (hasEdge src) = true := List.find?_some (p := fun pred => reached.any (hasEdge pred)) found
    obtain ⟨dst, reachedDst, actual⟩ := List.any_eq_true.mp reaches
    rw [List.unattach_filter (g := fun b => decide (b ≠ src)) (hf := fun _ _ => rfl),
      List.unattach_attach] at ih
    have seed : Q src := step src available dst actual (seeds dst reachedDst)
    have ⟨retains, sound, closed⟩ := ih
      (fun b hb => (List.mem_cons.mp hb).elim (fun eq => eq.symm ▸ seed) (seeds b))
      (fun b hb => step b (List.mem_filter.mp hb).1)
    refine ⟨fun b hb => retains b (List.mem_cons_of_mem _ hb), sound, ?_⟩
    intro pred hpred next hnext actual
    by_cases same : pred = src
    · exact retains pred (List.mem_cons.mpr (.inl same))
    · exact closed pred (List.mem_filter.mpr ⟨hpred, by simp [same]⟩) next hnext actual

private theorem members_iff (checked : checkBackedge tree blocks edge = true)
    (b : BlockId Label) : b ∈ members tree blocks edge ↔ Member cfg edge b := by
  letI := blockDecEq tree
  let header : BlockId Label := some edge.header
  let latch : BlockId Label := some edge.latch
  let remaining := (vertices blocks).filter fun b => decide (b ≠ header ∧ b ≠ latch)
  let seeds := if latch = header then [] else [latch]
  let closed := reverseClose (edge? tree) remaining seeds
  have reachable := mem_vertices_iff_reachable (backedgeChecks checked).1
  have ⟨retains, sound, predecessor⟩ := reverseClose_spec (edge? tree) (ToLatch cfg edge) remaining seeds
    (by
      intro node member
      by_cases same : latch = header
      · simp [seeds, same] at member
      · have eq : node = latch := by simpa [seeds, same] using member
        subst node
        exact .latch (checkBackedge_sound checked).2.1 (fun eq => same (congrArg some eq)))
    (by
      intro src mem dst actual path
      have ⟨inventory, avoids⟩ := List.mem_filter.mp mem
      obtain ⟨target, rfl, slot, actual⟩ := (edge_eq_true_iff src dst).mp actual
      exact .predecessor ((reachable src).mp inventory) (of_decide_eq_true avoids).1 slot actual path)
  have latchSeed (distinct : latch ≠ header) : latch ∈ closed :=
    retains latch (by simp [seeds, distinct])
  change b ∈ header :: closed ↔ b = header ∨ ToLatch cfg edge b
  rw [List.mem_cons]
  apply or_congr_right
  constructor
  · exact sound b
  · intro path
    induction path with
    | latch _ avoids => exact latchSeed (fun eq => avoids (Option.some.inj eq))
    | @predecessor src dst reaches avoids slot actual tail ih =>
      by_cases atLatch : src = latch
      · exact atLatch.symm ▸ latchSeed (atLatch ▸ avoids)
      · have available : src ∈ remaining := List.mem_filter.mpr
          ⟨(reachable src).mpr reaches, decide_eq_true ⟨avoids, atLatch⟩⟩
        exact predecessor src available (some dst) ih
          ((edge_eq_true_iff src (some dst)).mpr ⟨dst, rfl, slot, actual⟩)

private theorem checkedMembers_eq {loopMembers : List (BlockId Label)}
    (result : checkedMembers? tree blocks edge = some loopMembers) :
    checkBackedge tree blocks edge = true ∧ members tree blocks edge = loopMembers := by
  by_cases checked : checkBackedge tree blocks edge = true <;>
    simp_all [checkedMembers?]

theorem checkedMembers_iff {loopMembers : List (BlockId Label)}
    (result : checkedMembers? tree blocks edge = some loopMembers)
    (b : BlockId Label) : b ∈ loopMembers ↔ Member cfg edge b := by
  obtain ⟨checked, rfl⟩ := checkedMembers_eq result
  exact members_iff checked b

theorem depth_eq_one_iff {loopMembers : List (BlockId Label)}
    (result : checkedMembers? tree blocks edge = some loopMembers)
    (b : BlockId Label) : depth tree loopMembers b = 1 ↔ Member cfg edge b := by
  letI := blockDecEq tree
  simpa [depth] using checkedMembers_iff result b

theorem choosePlacement_sound {operands : List (Point Label)} {uses : List (Use Label)}
    {chosen : Point Label} (found : choosePlacement tree blocks edge operands uses = some chosen) :
    checkBackedge tree blocks edge = true ∧ chosen ∈ candidateCuts cfg blocks ∧
      Legal cfg operands uses chosen := by
  cases membersResult : checkedMembers? tree blocks edge with
  | none => simp [choosePlacement, membersResult] at found
  | some loopMembers =>
    exact ⟨(checkedMembers_eq membersResult).1,
      chooseLoopPlacement_sound tree (depth tree loopMembers) blocks operands uses
        (by simpa [choosePlacement, membersResult] using found)⟩

theorem choosePlacement_minimal {loopMembers : List (BlockId Label)}
    (result : checkedMembers? tree blocks edge = some loopMembers)
    {operands : List (Point Label)} {uses : List (Use Label)} {chosen other : Point Label}
    (found : choosePlacement tree blocks edge operands uses = some chosen)
    (candidate : other ∈ candidateCuts cfg blocks)
    (checked : checkPlacement tree operands uses other = true) :
    depth tree loopMembers chosen.block ≤ depth tree loopMembers other.block ∧
      (depth tree loopMembers chosen.block = depth tree loopMembers other.block →
        (tree.address other.block).length ≤ (tree.address chosen.block).length) :=
  chooseLoopPlacement_minimal tree (depth tree loopMembers) blocks operands uses
    (by simpa [choosePlacement, result] using found) candidate checked

theorem choosePlacement_complete (valid : checkBackedge tree blocks edge = true)
    (complete : tree.Complete) (operands : List (Point Label)) (uses : List (Use Label)) :
    choosePlacement tree blocks edge operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, ¬ Legal cfg operands uses point := by
  simpa [choosePlacement, checkedMembers?, valid] using
    chooseLoopPlacement_complete tree (depth tree (members tree blocks edge)) blocks operands uses complete

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop
