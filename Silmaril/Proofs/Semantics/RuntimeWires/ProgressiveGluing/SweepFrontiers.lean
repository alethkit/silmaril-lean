module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepCuts

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}

namespace LevelStack

variable {A B C : ℕ} {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable {g : Diagram S (L + R) C .point} (stack : LevelStack lower upper g)

/-- Pick the rescaled cuts of the two operands, using one actual seam cut. -/
noncomputable def spliceCuts (p : lower.LayerCuts) (q : upper.LayerCuts) : g.LayerCuts where
  height i :=
    if hl : i.val < lower.levelCount then halfHeight 0 (p.height ⟨i.val, by omega⟩)
    else if i.val = lower.levelCount then 1 / 2
    else halfHeight 1 (q.height ⟨i.val - lower.levelCount, by
      have hi := i.isLt.trans_eq (congrArg Nat.succ (count_glue stack))
      omega⟩)
  in_gap i := by
    split
    · next hl =>
      let j : Fin (lower.levelCount + 1) := ⟨i.val, by omega⟩
      have eq : lowerCut stack j = i := Fin.ext rfl
      exact Eq.mp (congrArg (fun ix => halfHeight 0 (p.height j) ∈ g.levelGap ix) eq)
        (lower_gap stack (p.in_gap j))
    · split
      · next hm =>
        exact (show joinCut stack = i from Fin.ext hm.symm) ▸ join_gap stack
      · next hl hm =>
        have hi := i.isLt.trans_eq (congrArg Nat.succ (count_glue stack))
        let j : Fin (upper.levelCount + 1) := ⟨i.val - lower.levelCount, by omega⟩
        have eq : upperCut stack j = i := by
          apply Fin.ext
          change lower.levelCount + (i.val - lower.levelCount) = i.val
          omega
        exact Eq.mp (congrArg (fun ix => halfHeight 1 (q.height j) ∈ g.levelGap ix) eq)
          (upper_gap stack (q.in_gap j))

theorem spliceCuts_lower (p : lower.LayerCuts) (q : upper.LayerCuts)
    (i : Fin (lower.levelCount + 1)) (before : i.val < lower.levelCount) :
    (spliceCuts stack p q).height (lowerCut stack i) = halfHeight 0 (p.height i) := by
  simp [spliceCuts, lowerCut, before]

theorem spliceCuts_upper (p : lower.LayerCuts) (q : upper.LayerCuts)
    (i : Fin (upper.levelCount + 1)) (after : 0 < i.val) :
    (spliceCuts stack p q).height (upperCut stack i) = halfHeight 1 (q.height i) := by
  have notBefore : ¬ lower.levelCount + i.val < lower.levelCount := by omega
  have nonzero : i ≠ 0 := by
    intro eq
    have : i.val = 0 := congrArg Fin.val eq
    omega
  simp [spliceCuts, upperCut, notBefore, nonzero]

theorem spliceCuts_join (p : lower.LayerCuts) (q : upper.LayerCuts) :
    (spliceCuts stack p q).height (joinCut stack) = 1 / 2 := by
  simp [spliceCuts, joinCut, lowerCut]

end LevelStack

theorem read_at {V : ℕ} {d : Diagram S V W .point} (s : d.LayerSweep)
    (i : Fin (d.levelCount + 1)) {h : ℝ} {ws : List (Fin W)}
    (gap : h ∈ d.levelGap i) (cut : d.OrderedCut h ws) : s.wires i = ws := by
  let cuts : d.LayerCuts :=
    ⟨fun j => if j = i then h else s.cuts.height j, fun j => by
      split
      · next eq => exact eq.symm ▸ gap
      · exact s.cuts.in_gap j⟩
  let t := d.layerSweepAt cuts
  have height : t.cuts.height i = h := by
    change (d.layerSweepAt cuts).cuts.height i = h
    rw [d.layerSweepAt_cuts]
    simp [cuts]
  exact (s.wires_eq t i).trans (Diagram.ordered_cut_unique (height ▸ t.ordered i) cut)

variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}
variable (m : lower.VerticalMatch upper)
variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : m.glue.LayerSweep)

theorem wires_lower (i : Fin (lower.levelCount + 1)) :
    s.wires ((matchedStack m).lowerCut i) = p.wires i :=
  read_at s _ ((matchedStack m).lower_gap (p.cuts.in_gap i))
    (cut_left m (lower.level_gap_regular (p.cuts.in_gap i)).1.2 (p.ordered i))

theorem wires_upper (i : Fin (upper.levelCount + 1)) :
    s.wires ((matchedStack m).upperCut i) = q.wires i :=
  read_at s _ ((matchedStack m).upper_gap (q.cuts.in_gap i))
    (cut_right m (upper.level_gap_regular (q.cuts.in_gap i)).1.1 (q.ordered i))

/-- The last lower cut reads the actual seam because every lower strand
ends on its top cap. -/
theorem ordered_join_lower : m.glue.OrderedCut (1 / 2) (p.wires (Fin.last lower.levelCount)) :=
  join_from_lower m (p.ordered _) (lower.level_gap_regular (p.cuts.in_gap _)).1.2
    (fun w => (p.output_mem w).mpr (m.lower_cap w))

theorem ordered_join_upper : m.glue.OrderedCut (1 / 2) (q.wires 0) :=
  join_from_upper m (q.ordered _) (upper.level_gap_regular (q.cuts.in_gap _)).1.1
    (fun w => (q.input_mem w).mpr (m.upper_cap w))

theorem wires_join_lower : s.wires ((matchedStack m).joinCut) = p.wires (Fin.last lower.levelCount) :=
  read_at s _ ((matchedStack m).join_gap) (ordered_join_lower m p)

theorem wires_first : s.wires 0 = p.wires 0 := by
  have eq : (matchedStack m).lowerCut 0 = 0 := rfl
  rw [← eq]
  exact wires_lower m p s 0

theorem wires_last : s.wires (Fin.last m.glue.levelCount) = q.wires (Fin.last upper.levelCount) := by
  have eq : (matchedStack m).upperCut (Fin.last upper.levelCount) = Fin.last m.glue.levelCount := by
    apply Fin.ext
    exact ((matchedStack m).count_glue).symm
  rw [← eq]
  exact wires_upper m q s _

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
