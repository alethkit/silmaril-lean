module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Geometry
public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Coordinates
import Mathlib.Tactic.Linarith

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B C : ℕ}

/-- The common height data of a two-slab gluing, independent of its wire IDs. -/
structure LevelStack (lower : Diagram S L A .point) (upper : Diagram S R B .point)
    (g : Diagram S (L + R) C .point) : Prop where
  lower_height : ∀ v, g.vertexHeight (Fin.castAdd R v) = halfHeight 0 (lower.vertexHeight v)
  upper_height : ∀ v, g.vertexHeight (Fin.natAdd L v) = halfHeight 1 (upper.vertexHeight v)

theorem matchedStack {lower : Diagram S L A .point} {upper : Diagram S R A .point}
    (m : lower.VerticalMatch upper) : LevelStack lower upper m.glue :=
  ⟨m.glue_height_left, m.glue_height_right⟩

theorem halfHeight_below {h : ℝ} (hh : h < 1) : halfHeight 0 h < 1 / 2 := by
  dsimp only [halfHeight]
  linarith

theorem halfHeight_above {h : ℝ} (hh : 0 < h) : (1 / 2 : ℝ) < halfHeight 1 h := by
  dsimp only [halfHeight]
  linarith

namespace LevelStack

variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable {g : Diagram S (L + R) C .point} (k : LevelStack lower upper g)

private theorem mem_levels_iff {V W : ℕ} (d : Diagram S V W .point) (h : ℝ) :
    h ∈ d.levels ↔ ∃ j, d.vertexHeight j = h := by
  simp [Diagram.levels]

include k

theorem levels_glue :
    g.levels = lower.levels.map (halfHeight 0) ++ upper.levels.map (halfHeight 1) := by
  let a := lower.levels.map (halfHeight 0)
  let b := upper.levels.map (halfHeight 1)
  have sorted (V W : ℕ) (d : Diagram S V W .point) : d.levels.Pairwise (· < ·) :=
    List.pairwise_iff_getElem.mpr (fun i j hi hj h => d.level_strict (show (⟨i, hi⟩ : Fin d.levelCount) < ⟨j, hj⟩ from h))
  have sorted' : (a ++ b).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · exact List.pairwise_map.mpr ((sorted L A lower).imp (fun h => halfHeight_strictMono 0 h))
    · exact List.pairwise_map.mpr ((sorted R B upper).imp (fun h => halfHeight_strictMono 1 h))
    · intro x hx y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      obtain ⟨j, rfl⟩ := (mem_levels_iff lower s).mp hs
      obtain ⟨v, rfl⟩ := (mem_levels_iff upper t).mp ht
      exact (halfHeight_below (lower.vertex_inside j).2.2).trans
        (halfHeight_above (upper.vertex_inside v).2.1)
  have same (h : ℝ) : h ∈ g.levels ↔ h ∈ a ++ b := by
    simp only [mem_levels_iff, List.mem_append, a, b, List.mem_map]
    constructor
    · rintro ⟨j, rfl⟩
      induction j using Fin.addCases with
      | left j => exact Or.inl ⟨_, ⟨j, rfl⟩, (k.lower_height j).symm⟩
      | right j => exact Or.inr ⟨_, ⟨j, rfl⟩, (k.upper_height j).symm⟩
    · rintro (⟨s, ⟨j, rfl⟩, rfl⟩ | ⟨t, ⟨j, rfl⟩, rfl⟩)
      · exact ⟨_, k.lower_height j⟩
      · exact ⟨_, k.upper_height j⟩
  have sortedGlue := sorted (L + R) C g
  have perm := (List.perm_ext_iff_of_nodup
    (sortedGlue.imp fun h => ne_of_lt h) (sorted'.imp fun h => ne_of_lt h)).mpr same
  exact perm.eq_of_pairwise (fun _ _ _ _ h k => (lt_asymm h k).elim) sortedGlue sorted'

theorem count_glue : g.levelCount = lower.levelCount + upper.levelCount := by
  simp only [Diagram.levelCount, levels_glue k, List.length_append, List.length_map]

noncomputable def lowerLevel (i : Fin lower.levelCount) : Fin g.levelCount :=
  ⟨i.val, by rw [count_glue k]; exact i.isLt.trans_le (Nat.le_add_right _ _)⟩

noncomputable def upperLevel (i : Fin upper.levelCount) : Fin g.levelCount :=
  ⟨lower.levelCount + i.val, by rw [count_glue k]; exact Nat.add_lt_add_left i.isLt _⟩

theorem height_lower (i : Fin lower.levelCount) :
    g.levelHeight (lowerLevel k i) = halfHeight 0 (lower.levelHeight i) := by
  change g.levels[(lowerLevel k i).val]'(lowerLevel k i).isLt = _
  simp only [levels_glue k]
  have bound : (lowerLevel k i).val < (lower.levels.map (halfHeight 0)).length := by
    simpa only [lowerLevel, List.length_map, Diagram.levelCount] using i.isLt
  rw [List.getElem_append_left bound, List.getElem_map]
  rfl

theorem height_upper (i : Fin upper.levelCount) :
    g.levelHeight (upperLevel k i) = halfHeight 1 (upper.levelHeight i) := by
  change g.levels[(upperLevel k i).val]'(upperLevel k i).isLt = _
  simp only [levels_glue k]
  have bound : (lower.levels.map (halfHeight 0)).length ≤ (upperLevel k i).val := by
    simpa only [upperLevel, List.length_map, Diagram.levelCount] using
      Nat.le_add_right lower.levelCount i.val
  rw [List.getElem_append_right bound, List.getElem_map]
  simp only [upperLevel, List.length_map, Diagram.levelCount, Nat.add_sub_cancel_left]
  rfl

end LevelStack
end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
