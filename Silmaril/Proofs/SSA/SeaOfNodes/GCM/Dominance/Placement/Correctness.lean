module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance
open Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {blocks : List (Target Label)}
variable {operands : List (Point Label)} {uses : List (Use Label)} {candidate : Point Label}
variable [DecidableEq (Target Label)]

theorem checkCut_iff : checkCut cfg blocks operands uses candidate = true ↔
    checkClosed cfg blocks = true ∧ Legal cfg operands uses candidate := by
  rw [checkCut, Bool.and_eq_true]
  refine and_congr_right fun closed => ?_
  have valid_iff (point : Point Label) :
      (reachable? cfg blocks point.block && decide (point.cut ≤ (shape cfg point.block).bindings)) =
        true ↔ point.Valid cfg := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, reachable?_iff closed, Point.Valid]
  have available_iff (defSite read : Point Label) (valid : read.Valid cfg) :
      (dominates? cfg blocks defSite.block read.block = true ∧
        decide (defSite.block = read.block → defSite.cut ≤ read.cut) = true) ↔
          defSite.AvailableAt cfg read := by
    simp only [decide_eq_true_eq, dominates?_iff, closed, valid.1, true_and]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.dominates, h.local_order⟩⟩
  simp only [checkPlacementWith, Bool.and_eq_true, List.all_eq_true, valid_iff]
  constructor
  · rintro ⟨⟨valid, inputs⟩, outputs⟩
    refine ⟨valid, ?_, ?_⟩
    · intro operand member
      obtain ⟨operandValid, available⟩ := inputs operand member
      exact ⟨operandValid, (available_iff operand candidate valid).mp available⟩
    · intro use member
      have accepted := outputs use member
      cases resolved : use.point? cfg with
      | none => simp [resolved] at accepted
      | some point =>
        simp only [resolved, Option.any_some, Bool.and_eq_true, valid_iff] at accepted
        exact ⟨point, rfl, accepted.1, (available_iff candidate point accepted.1).mp accepted.2⟩
  · intro legal
    refine ⟨⟨legal.candidate_valid, ?_⟩, ?_⟩
    · intro operand member
      obtain ⟨valid, available⟩ := legal.operands_available operand member
      exact ⟨valid, (available_iff operand candidate legal.candidate_valid).mpr available⟩
    · intro use member
      obtain ⟨point, resolved, valid, available⟩ := legal.uses_available use member
      simp only [resolved, Option.any_some, Bool.and_eq_true, valid_iff]
      exact ⟨valid, (available_iff candidate point valid).mpr available⟩

theorem discoverCut_sound (found : discoverCut cfg blocks operands uses = some candidate) :
    candidate ∈ candidateCuts cfg blocks ∧
      checkClosed cfg blocks = true ∧ Legal cfg operands uses candidate :=
  ⟨List.mem_of_find?_eq_some found, checkCut_iff.mp (List.find?_some found)⟩

theorem discoverCut_eq_none_iff (closed : checkClosed cfg blocks = true) :
    discoverCut cfg blocks operands uses = none ↔
      ∀ point, ¬ Legal cfg operands uses point := by
  simp only [discoverCut, List.find?_eq_none]
  constructor
  · intro rejected point legal
    obtain ⟨past, path⟩ := legal.candidate_valid.1
    have listed : point ∈ candidateCuts cfg blocks :=
      (mem_candidateCuts blocks point).mpr ⟨path_endpoint_mem closed path, legal.candidate_valid.2⟩
    exact rejected point listed (checkCut_iff.mpr ⟨closed, legal⟩)
  · intro illegal point _ accepted
    exact illegal point (checkCut_iff.mp accepted).2

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement
