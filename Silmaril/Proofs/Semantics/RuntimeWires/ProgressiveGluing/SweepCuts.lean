module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepLevels
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Cuts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

namespace LevelStack

variable {O : Type u} {S : Signature.{u,v} O} {L R A B C : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable {g : Diagram S (L + R) C .point} (stack : LevelStack lower upper g)

private theorem gap_iff {V W : ℕ} (d : Diagram S V W .point)
    (i : Fin (d.levelCount + 1)) (h : ℝ) :
    h ∈ d.levelGap i ↔ h ∈ Set.Ioo 0 1 ∧
      (∀ j : Fin d.levelCount, j.val < i.val → d.levelHeight j < h) ∧
      (∀ j : Fin d.levelCount, i.val ≤ j.val → h < d.levelHeight j) := by
  have atZero : d.levelLandmark 0 = 0 := by simp [Diagram.levelLandmark]
  have atLast : d.levelLandmark (Fin.last (d.levelCount + 1)) = 1 := by
    simp [Diagram.levelLandmark]
  have atLevel (j : Fin d.levelCount) : d.levelLandmark j.castSucc.succ = d.levelHeight j := by
    simp [Diagram.levelLandmark]
  constructor
  · intro gap
    refine ⟨(d.level_gap_regular gap).1, ?_, ?_⟩
    · intro j hj
      rw [← atLevel]
      exact (d.level_landmarks_strict.monotone (show j.castSucc.succ ≤ i.castSucc from
        Nat.succ_le_of_lt hj)).trans_lt gap.1
    · intro j hj
      rw [← atLevel]
      exact gap.2.trans_le (d.level_landmarks_strict.monotone (show i.succ ≤ j.castSucc.succ from
        Nat.succ_le_succ hj))
  · rintro ⟨inside, below, above⟩
    change d.levelLandmark i.castSucc < h ∧ h < d.levelLandmark i.succ
    constructor
    · by_cases first : i.val = 0
      · rw [show i.castSucc = 0 from Fin.ext first, atZero]
        exact inside.1
      · let j : Fin d.levelCount := ⟨i.val - 1, by have := i.isLt; omega⟩
        have hj : j.val < i.val := by dsimp [j]; omega
        have eq : i.castSucc = j.castSucc.succ := by apply Fin.ext; dsimp [j]; omega
        rw [eq, atLevel]
        exact below j hj
    · by_cases last : i.val = d.levelCount
      · rw [show i.succ = Fin.last (d.levelCount + 1) from Fin.ext (congrArg Nat.succ last), atLast]
        exact inside.2
      · let j : Fin d.levelCount := ⟨i.val, by have := i.isLt; omega⟩
        have eq : i.succ = j.castSucc.succ := rfl
        rw [eq, atLevel]
        exact above j le_rfl

private theorem level_inside {V W : ℕ} (d : Diagram S V W .point) (i : Fin d.levelCount) :
    d.levelHeight i ∈ Set.Ioo 0 1 := by
  obtain ⟨v, hv⟩ := d.vertex_at_level i
  exact hv ▸ (d.vertex_inside v).2

noncomputable def lowerCut (i : Fin (lower.levelCount + 1)) : Fin (g.levelCount + 1) :=
  ⟨i.val, by rw [count_glue stack]; have := i.isLt; omega⟩

noncomputable def upperCut (i : Fin (upper.levelCount + 1)) : Fin (g.levelCount + 1) :=
  ⟨lower.levelCount + i.val, by rw [count_glue stack]; have := i.isLt; omega⟩

noncomputable def joinCut : Fin (g.levelCount + 1) := lowerCut stack (Fin.last lower.levelCount)

theorem upper_join : upperCut stack 0 = joinCut stack := by apply Fin.ext; simp [upperCut, joinCut, lowerCut]

theorem join_gap : (1 / 2 : ℝ) ∈ g.levelGap (joinCut stack) := by
  refine (gap_iff _ _ _).mpr ⟨by norm_num, ?_, ?_⟩
  · intro j hj
    have bound : j.val < lower.levelCount := hj
    let i : Fin lower.levelCount := ⟨j.val, bound⟩
    have eq : j = lowerLevel stack i := rfl
    rw [eq, height_lower]
    exact halfHeight_below (level_inside lower i).2
  · intro j hj
    have bound : lower.levelCount ≤ j.val := hj
    have hj' : j.val < lower.levelCount + upper.levelCount :=
      j.isLt.trans_eq (count_glue stack)
    let i : Fin upper.levelCount := ⟨j.val - lower.levelCount, by omega⟩
    have eq : j = upperLevel stack i := by
      apply Fin.ext
      change j.val = lower.levelCount + (j.val - lower.levelCount)
      omega
    rw [eq, height_upper]
    exact halfHeight_above (level_inside upper i).1

theorem lower_gap {i : Fin (lower.levelCount + 1)} {h : ℝ}
    (gap : h ∈ lower.levelGap i) : halfHeight 0 h ∈ g.levelGap (lowerCut stack i) := by
  obtain ⟨inside, below, above⟩ := (gap_iff _ _ _).mp gap
  have mid := halfHeight_below inside.2
  have positive : 0 < halfHeight 0 h := by dsimp [halfHeight]; linarith [inside.1]
  refine (gap_iff _ _ _).mpr ⟨⟨positive, mid.trans (by norm_num)⟩, ?_, ?_⟩
  · intro j hj
    change j.val < i.val at hj
    let k : Fin lower.levelCount := ⟨j.val, by have := i.isLt; omega⟩
    have eq : j = lowerLevel stack k := rfl
    rw [eq, height_lower]
    exact halfHeight_strictMono 0 (below k hj)
  · intro j hj
    change i.val ≤ j.val at hj
    by_cases left : j.val < lower.levelCount
    · let k : Fin lower.levelCount := ⟨j.val, left⟩
      have eq : j = lowerLevel stack k := rfl
      rw [eq, height_lower]
      exact halfHeight_strictMono 0 (above k hj)
    · have hj' : j.val < lower.levelCount + upper.levelCount :=
        j.isLt.trans_eq (count_glue stack)
      let k : Fin upper.levelCount := ⟨j.val - lower.levelCount, by omega⟩
      have eq : j = upperLevel stack k := by
        apply Fin.ext
        change j.val = lower.levelCount + (j.val - lower.levelCount)
        omega
      rw [eq, height_upper]
      exact mid.trans (halfHeight_above (level_inside upper k).1)

theorem upper_gap {i : Fin (upper.levelCount + 1)} {h : ℝ}
    (gap : h ∈ upper.levelGap i) : halfHeight 1 h ∈ g.levelGap (upperCut stack i) := by
  obtain ⟨inside, below, above⟩ := (gap_iff _ _ _).mp gap
  have mid := halfHeight_above inside.1
  have top : halfHeight 1 h < 1 := by dsimp [halfHeight]; linarith [inside.2]
  refine (gap_iff _ _ _).mpr ⟨⟨(by norm_num : (0 : ℝ) < 1 / 2).trans mid, top⟩, ?_, ?_⟩
  · intro j hj
    change j.val < lower.levelCount + i.val at hj
    by_cases left : j.val < lower.levelCount
    · let k : Fin lower.levelCount := ⟨j.val, left⟩
      have eq : j = lowerLevel stack k := rfl
      rw [eq, height_lower]
      exact (halfHeight_below (level_inside lower k).2).trans mid
    · have hj' : j.val < lower.levelCount + upper.levelCount :=
        j.isLt.trans_eq (count_glue stack)
      let k : Fin upper.levelCount := ⟨j.val - lower.levelCount, by omega⟩
      have eq : j = upperLevel stack k := by
        apply Fin.ext
        change j.val = lower.levelCount + (j.val - lower.levelCount)
        omega
      rw [eq, height_upper]
      exact halfHeight_strictMono 1 (below k (by dsimp [k]; omega))
  · intro j hj
    change lower.levelCount + i.val ≤ j.val at hj
    have hj' : j.val < lower.levelCount + upper.levelCount :=
      j.isLt.trans_eq (count_glue stack)
    let k : Fin upper.levelCount := ⟨j.val - lower.levelCount, by omega⟩
    have eq : j = upperLevel stack k := by
      apply Fin.ext
      change j.val = lower.levelCount + (j.val - lower.levelCount)
      omega
    rw [eq, height_upper]
    exact halfHeight_strictMono 1 (above k (by dsimp [k]; omega))

end LevelStack
end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
