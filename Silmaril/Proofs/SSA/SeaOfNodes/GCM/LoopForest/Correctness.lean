module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs
import Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopForest
open Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop
  (Backedge Member blockDecEq checkInventory slots mem_vertices_iff_reachable)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}
variable {tree : DominatorTree cfg} {blocks : List (Target Label)}

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨by simp [List.mem_eraseDups], eraseDups_nodup _⟩
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem some_mem_vertices (label : Target Label) :
    some label ∈ NaturalLoop.vertices blocks ↔ label ∈ blocks := by
  simp [NaturalLoop.vertices]

private theorem scan_spec (edge : Backedge Label) :
    edge ∈ scan tree blocks ↔ edge.latch ∈ blocks ∧
      (shape cfg (some edge.latch)).target edge.slot = some edge.header ∧
      List.IsPrefix (tree.address (some edge.header)) (tree.address (some edge.latch)) := by
  letI := targetDecEq tree
  have slot_mem (slot : EdgeSlot) : slot ∈ slots := by cases slot <;> decide
  cases edge with
  | mk header latch slot =>
    change _ ∈ blocks.eraseDups.flatMap _ ↔ _
    simp only [List.mem_flatMap, List.mem_eraseDups, List.mem_filterMap]
    constructor
    · rintro ⟨source, inBlocks, occurrence, _, found⟩
      change (shape cfg (some source)).target occurrence >>= _ = _ at found
      obtain ⟨target, actual, picked⟩ := Option.bind_eq_some_iff.mp found
      split at picked
      · cases picked
        exact ⟨inBlocks, actual, List.isPrefixOf_iff_prefix.mp ‹_›⟩
      · contradiction
    · rintro ⟨inBlocks, actual, ancestor⟩
      refine ⟨latch, inBlocks, slot, slot_mem slot, ?_⟩
      apply Option.bind_eq_some_iff.mpr
      exact ⟨header, actual, ite_eq_left (List.isPrefixOf_iff_prefix.mpr ancestor)⟩

private theorem discover_eq {edges : List (Backedge Label)}
    (result : discover? tree blocks = some edges) :
    checkInventory tree blocks = true ∧ scan tree blocks = edges := by
  by_cases checked : checkInventory tree blocks = true <;> simp_all [discover?]

private theorem scan_checked (inventory : checkInventory tree blocks = true)
    {edge : Backedge Label} (member : edge ∈ scan tree blocks) :
    NaturalLoop.checkBackedge tree blocks edge = true := by
  letI := blockDecEq tree
  obtain ⟨latch, actual, ancestor⟩ := (scan_spec edge).mp member
  have inLatch := (some_mem_vertices edge.latch).mpr latch
  obtain ⟨past, path⟩ := (mem_vertices_iff_reachable inventory _).mp inLatch
  have inHeader := (mem_vertices_iff_reachable inventory _).mpr ⟨_, path.step edge.slot actual⟩
  simp only [NaturalLoop.checkBackedge, Bool.and_eq_true, decide_eq_true_eq,
    List.isPrefixOf_iff_prefix]
  exact ⟨⟨inventory, inHeader, inLatch⟩, actual, ancestor⟩

theorem discover_sound {edges : List (Backedge Label)}
    (result : discover? tree blocks = some edges) {edge : Backedge Label}
    (member : edge ∈ edges) : ActualBackedge cfg edge := by
  obtain ⟨inventory, rfl⟩ := discover_eq result
  exact (NaturalLoop.checkBackedge_sound (scan_checked inventory member)).2

theorem mem_discover_iff {edges : List (Backedge Label)}
    (result : discover? tree blocks = some edges) (complete : tree.Complete)
    (edge : Backedge Label) : edge ∈ edges ↔ ActualBackedge cfg edge := by
  refine ⟨discover_sound result, ?_⟩
  obtain ⟨inventory, rfl⟩ := discover_eq result
  rintro ⟨latch, actual, dominates⟩
  exact (scan_spec edge).mpr ⟨(some_mem_vertices edge.latch).mp
    ((mem_vertices_iff_reachable inventory _).mpr latch), actual,
    complete.prefix_complete latch dominates⟩

private theorem loops_eq {loops : List (HeaderLoop Label)}
    (result : loops? tree blocks = some loops) :
    ∃ edges, discover? tree blocks = some edges ∧ coalesce tree blocks edges = loops :=
  Option.map_eq_some_iff.mp result

theorem loopHeaders_nodup {loops : List (HeaderLoop Label)}
    (result : loops? tree blocks = some loops) : (loops.map HeaderLoop.header).Nodup := by
  letI := targetDecEq tree
  obtain ⟨edges, _, rfl⟩ := loops_eq result
  simpa [coalesce, List.map_map, Function.comp_def] using
    eraseDups_nodup (edges.map Backedge.header)

theorem mem_loopHeaders_iff {loops : List (HeaderLoop Label)}
    (result : loops? tree blocks = some loops) (complete : tree.Complete)
    (header : Target Label) : header ∈ loops.map HeaderLoop.header ↔
      ∃ edge, ActualBackedge cfg edge ∧ edge.header = header := by
  obtain ⟨edges, found, rfl⟩ := loops_eq result
  simp [coalesce, List.map_map, Function.comp_def, List.mem_eraseDups, List.mem_map,
    mem_discover_iff found complete]

theorem mem_loop_iff {loops : List (HeaderLoop Label)}
    (result : loops? tree blocks = some loops) (complete : tree.Complete)
    {loop : HeaderLoop Label} (listed : loop ∈ loops) (b : BlockId Label) :
    b ∈ loop.members ↔
      ∃ edge, ActualBackedge cfg edge ∧ edge.header = loop.header ∧ Member cfg edge b := by
  obtain ⟨edges, found, rfl⟩ := loops_eq result
  obtain ⟨header, _, rfl⟩ := List.mem_map.mp listed
  simp only [List.mem_eraseDups, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  obtain ⟨inventory, scanned⟩ := discover_eq found
  have member_iff (edge : Backedge Label) (inEdges : edge ∈ edges) :
      b ∈ NaturalLoop.members tree blocks edge ↔ Member cfg edge b := by
    have checked := scan_checked inventory (scanned ▸ inEdges : edge ∈ scan tree blocks)
    exact NaturalLoop.checkedMembers_iff (tree := tree) (blocks := blocks)
      (by simp [NaturalLoop.checkedMembers?, checked]) b
  constructor
  · rintro ⟨edge, ⟨inEdges, same⟩, member⟩
    exact ⟨edge, (mem_discover_iff found complete edge).mp inEdges, same, (member_iff edge inEdges).mp member⟩
  · rintro ⟨edge, actual, same, member⟩
    have inEdges := (mem_discover_iff found complete edge).mpr actual
    exact ⟨edge, ⟨inEdges, same⟩, (member_iff edge inEdges).mpr member⟩

theorem forest_eq_some_iff (loops : List (HeaderLoop Label)) :
    forest? tree blocks = some loops ↔ loops? tree blocks = some loops ∧ loops.Pairwise Compatible := by
  cases found : loops? tree blocks with
  | none => simp [forest?, found]
  | some family =>
    have accepts : checkLaminar tree family = true ↔ family.Pairwise Compatible := by
      simp only [checkLaminar, decide_eq_true_eq]
    by_cases checked : checkLaminar tree family = true
    · simp [forest?, found, checked]
      rintro rfl
      exact accepts.mp checked
    · simp [forest?, found, checked]
      rintro rfl
      exact fun laminar => checked (accepts.mpr laminar)

theorem enclosing_spec {loops : List (HeaderLoop Label)}
    (admitted : forest? tree blocks = some loops) (complete : tree.Complete)
    (b : BlockId Label) :
    let family := enclosing tree loops b
    (family.map HeaderLoop.header).Nodup ∧
      family.Pairwise (fun a b => StrictInside a b ∨ StrictInside b a) ∧
      ∀ header, header ∈ family.map HeaderLoop.header ↔
        ∃ edge, ActualBackedge cfg edge ∧ edge.header = header ∧ Member cfg edge b := by
  letI := blockDecEq tree
  obtain ⟨found, laminar⟩ := (forest_eq_some_iff loops).mp admitted
  have inside (loop : HeaderLoop Label) :
      loop ∈ enclosing tree loops b ↔ loop ∈ loops ∧ b ∈ loop.members := by
    simp [enclosing]
  have noDuplicates := loopHeaders_nodup found
  refine ⟨List.pairwise_map.mpr ((List.pairwise_map.mp noDuplicates).filter _), ?_, ?_⟩
  · refine (laminar.filter _).imp_of_mem ?_
    intro a c inA inC nested
    exact nested.resolve_left (fun disjoint => disjoint b ((inside a).mp inA).2 ((inside c).mp inC).2)
  · intro header
    simp only [List.mem_map, inside]
    constructor
    · rintro ⟨loop, ⟨listed, contains⟩, rfl⟩
      exact (mem_loop_iff found complete listed b).mp contains
    · rintro ⟨edge, actual, same, member⟩
      obtain ⟨loop, listed, headerEq⟩ := List.mem_map.mp
        ((mem_loopHeaders_iff found complete header).mpr ⟨edge, actual, same⟩)
      exact ⟨loop, ⟨listed, (mem_loop_iff found complete listed b).mpr
        ⟨edge, actual, same.trans headerEq.symm, member⟩⟩, headerEq⟩

theorem choosePlacement_sound {operands : List (Point Label)} {uses : List (Use Label)}
    {chosen : Point Label} (found : choosePlacement tree blocks operands uses = some chosen) :
    chosen ∈ candidateCuts cfg blocks ∧ Legal cfg operands uses chosen := by
  cases admission : forest? tree blocks with
  | none => simp [choosePlacement, admission] at found
  | some loops =>
    exact chooseLoopPlacement_sound tree (depth tree loops) blocks operands uses
      (by simpa [choosePlacement, admission] using found)

theorem choosePlacement_minimal {loops : List (HeaderLoop Label)}
    (admitted : forest? tree blocks = some loops)
    {operands : List (Point Label)} {uses : List (Use Label)} {chosen other : Point Label}
    (found : choosePlacement tree blocks operands uses = some chosen)
    (candidate : other ∈ candidateCuts cfg blocks)
    (checked : checkPlacement tree operands uses other = true) :
    depth tree loops chosen.block ≤ depth tree loops other.block ∧
      (depth tree loops chosen.block = depth tree loops other.block →
        (tree.address other.block).length ≤ (tree.address chosen.block).length) :=
  chooseLoopPlacement_minimal tree (depth tree loops) blocks operands uses
    (by simpa [choosePlacement, admitted] using found) candidate checked

theorem choosePlacement_complete {loops : List (HeaderLoop Label)}
    (admitted : forest? tree blocks = some loops)
    (complete : tree.Complete) (operands : List (Point Label)) (uses : List (Use Label)) :
    choosePlacement tree blocks operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, ¬ Legal cfg operands uses point := by
  simpa [choosePlacement, admitted] using
    chooseLoopPlacement_complete tree (depth tree loops) blocks operands uses complete

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest
