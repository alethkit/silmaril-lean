module

public import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}
variable {operands : List (Point Label)} {uses : List (Use Label)} {candidate : Point Label}

theorem mem_candidateCuts (blocks : List (Target Label)) (point : Point Label) :
    point ∈ candidateCuts cfg blocks ↔
      point.block ∈ (none :: blocks.map some) ∧ point.cut ≤ (shape cfg point.block).bindings := by
  constructor
  · intro member
    obtain ⟨block, inList, inBlock⟩ := List.mem_flatMap.mp member
    obtain ⟨cut, inRange, rfl⟩ := List.mem_map.mp inBlock
    exact ⟨inList, Nat.lt_succ_iff.mp (List.mem_range.mp inRange)⟩
  · rintro ⟨inList, inRange⟩
    exact List.mem_flatMap.mpr ⟨point.block, inList, List.mem_map.mpr
      ⟨point.cut, List.mem_range.mpr (Nat.lt_succ_iff.mpr inRange), rfl⟩⟩

theorem discoverPlacement_sound (tree : DominatorTree cfg) (blocks : List (Target Label))
    (found : discoverPlacement tree blocks operands uses = some candidate) :
    candidate ∈ candidateCuts cfg blocks ∧ checkPlacement tree operands uses candidate = true :=
  ⟨List.mem_of_find?_eq_some found, List.find?_some found⟩

theorem discoverPlacement_eq_none_iff (tree : DominatorTree cfg) (blocks : List (Target Label))
    (operands : List (Point Label)) (uses : List (Use Label)) :
    discoverPlacement tree blocks operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, checkPlacement tree operands uses point = false := by
  simp only [discoverPlacement, List.find?_eq_none, Bool.not_eq_true]

private theorem valid_check {tree : DominatorTree cfg} (complete : tree.Complete)
    {point : Point Label} (valid : point.Valid cfg) : point.valid? tree = true := by
  simp only [Point.valid?, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨complete.reachable_complete valid.1, valid.2⟩

private theorem available_check {tree : DominatorTree cfg} (complete : tree.Complete)
    {defSite read : Point Label} (reachable : Reachable cfg read.block)
    (available : defSite.AvailableAt cfg read) : defSite.available? tree read = true := by
  simp only [Point.available?, Bool.and_eq_true, List.isPrefixOf_iff_prefix, decide_eq_true_eq]
  exact ⟨complete.prefix_complete reachable available.dominates,
    fun same => available.local_order (tree.address_injective same)⟩

private theorem check_of_legal {tree : DominatorTree cfg} (complete : tree.Complete)
    (legal : Legal cfg operands uses candidate) : checkPlacement tree operands uses candidate = true := by
  simp only [checkPlacement, checkPlacementWith, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨valid_check complete legal.candidate_valid, ?_⟩, ?_⟩
  · intro operand member
    obtain ⟨valid, available⟩ := legal.operands_available operand member
    exact ⟨valid_check complete valid, available_check complete legal.candidate_valid.1 available⟩
  · intro use member
    obtain ⟨point, resolved, valid, available⟩ := legal.uses_available use member
    rw [resolved, Option.any_some, Bool.and_eq_true]
    exact ⟨valid_check complete valid, available_check complete valid.1 available⟩

theorem discoverPlacement_eq_none_iff_no_legal (tree : DominatorTree cfg) (complete : tree.Complete)
    (blocks : List (Target Label)) (operands : List (Point Label)) (uses : List (Use Label)) :
    discoverPlacement tree blocks operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, ¬ Legal cfg operands uses point := by
  rw [discoverPlacement_eq_none_iff]
  constructor
  · intro rejected point member legal
    exact Bool.noConfusion ((rejected point member).symm.trans (check_of_legal complete legal))
  · intro illegal point member
    cases checked : checkPlacement tree operands uses point with
    | false => rfl
    | true => exact (illegal point member (checkPlacement_sound tree checked)).elim

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery
