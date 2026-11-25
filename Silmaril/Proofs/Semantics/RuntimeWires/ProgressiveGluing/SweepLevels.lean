module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Geometry
public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Coordinates
import Mathlib.Tactic.Linarith

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

theorem halfHeight_below {h : ℝ} (hh : h < 1) : halfHeight 0 h < 1 / 2 := by
  dsimp only [halfHeight]
  linarith

theorem halfHeight_above {h : ℝ} (hh : 0 < h) : (1 / 2 : ℝ) < halfHeight 1 h := by
  dsimp only [halfHeight]
  linarith

private theorem mem_levels_iff {V : ℕ} (d : Diagram S V W .point) (h : ℝ) :
    h ∈ d.levels ↔ ∃ j, d.vertexHeight j = h := by
  simp [Diagram.levels]

theorem levels_glue :
    m.glue.levels = lower.levels.map (halfHeight 0) ++ upper.levels.map (halfHeight 1) := by
  let a := lower.levels.map (halfHeight 0)
  let b := upper.levels.map (halfHeight 1)
  have sorted (V : ℕ) (d : Diagram S V W .point) : d.levels.Pairwise (· < ·) :=
    List.pairwise_iff_getElem.mpr (fun i j hi hj h => d.level_strict (show (⟨i, hi⟩ : Fin d.levelCount) < ⟨j, hj⟩ from h))
  have sorted' : (a ++ b).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · exact List.pairwise_map.mpr ((sorted L lower).imp (fun h => halfHeight_strictMono 0 h))
    · exact List.pairwise_map.mpr ((sorted R upper).imp (fun h => halfHeight_strictMono 1 h))
    · intro x hx y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      obtain ⟨j, rfl⟩ := (mem_levels_iff lower s).mp hs
      obtain ⟨k, rfl⟩ := (mem_levels_iff upper t).mp ht
      exact (halfHeight_below (lower.vertex_inside j).2.2).trans
        (halfHeight_above (upper.vertex_inside k).2.1)
  have same (h : ℝ) : h ∈ m.glue.levels ↔ h ∈ a ++ b := by
    simp only [mem_levels_iff, List.mem_append, a, b, List.mem_map]
    constructor
    · rintro ⟨j, rfl⟩
      induction j using Fin.addCases with
      | left j => exact Or.inl ⟨_, ⟨j, rfl⟩, (m.glue_height_left j).symm⟩
      | right j => exact Or.inr ⟨_, ⟨j, rfl⟩, (m.glue_height_right j).symm⟩
    · rintro (⟨s, ⟨j, rfl⟩, rfl⟩ | ⟨t, ⟨j, rfl⟩, rfl⟩)
      · exact ⟨_, m.glue_height_left j⟩
      · exact ⟨_, m.glue_height_right j⟩
  have sortedGlue := sorted (L + R) m.glue
  have perm := (List.perm_ext_iff_of_nodup
    (sortedGlue.imp fun h => ne_of_lt h) (sorted'.imp fun h => ne_of_lt h)).mpr same
  exact perm.eq_of_pairwise (fun _ _ _ _ h k => (lt_asymm h k).elim) sortedGlue sorted'

theorem count_glue : m.glue.levelCount = lower.levelCount + upper.levelCount := by
  simp only [Diagram.levelCount, levels_glue m, List.length_append, List.length_map]

noncomputable def lowerLevel (i : Fin lower.levelCount) : Fin m.glue.levelCount :=
  ⟨i.val, by rw [count_glue m]; exact i.isLt.trans_le (Nat.le_add_right _ _)⟩

noncomputable def upperLevel (i : Fin upper.levelCount) : Fin m.glue.levelCount :=
  ⟨lower.levelCount + i.val, by rw [count_glue m]; exact Nat.add_lt_add_left i.isLt _⟩

theorem height_lower (i : Fin lower.levelCount) :
    m.glue.levelHeight (lowerLevel m i) = halfHeight 0 (lower.levelHeight i) := by
  change m.glue.levels[(lowerLevel m i).val]'(lowerLevel m i).isLt = _
  simp only [levels_glue m]
  have bound : (lowerLevel m i).val < (lower.levels.map (halfHeight 0)).length := by
    simpa only [lowerLevel, List.length_map, Diagram.levelCount] using i.isLt
  rw [List.getElem_append_left bound, List.getElem_map]
  rfl

theorem height_upper (i : Fin upper.levelCount) :
    m.glue.levelHeight (upperLevel m i) = halfHeight 1 (upper.levelHeight i) := by
  change m.glue.levels[(upperLevel m i).val]'(upperLevel m i).isLt = _
  simp only [levels_glue m]
  have bound : (lower.levels.map (halfHeight 0)).length ≤ (upperLevel m i).val := by
    simpa only [upperLevel, List.length_map, Diagram.levelCount] using
      Nat.le_add_right lower.levelCount i.val
  rw [List.getElem_append_right bound, List.getElem_map]
  simp only [upperLevel, List.length_map, Diagram.levelCount, Nat.add_sub_cancel_left]
  rfl

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
