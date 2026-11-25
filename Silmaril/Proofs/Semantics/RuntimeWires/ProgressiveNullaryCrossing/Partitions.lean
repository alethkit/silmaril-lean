module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Geometry

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : Diagram S V W .point} {moved other : Fin V} {s : d.NullarySlide moved}
variable (c : s.Crossing other)
variable (p : c.tied.PairSlice moved other c.lowerCut c.upperCut)

theorem no_inputs {h : ℝ} (valid : h ∈ Set.Icc s.bottom s.top) :
    (s.atHeight h valid).inputs moved = [] := by
  change d.inputs moved = []
  exact List.eq_nil_of_length_eq_zero (by simp [Diagram.inputs, s.no_inputs])

theorem no_outputs {h : ℝ} (valid : h ∈ Set.Icc s.bottom s.top) :
    (s.atHeight h valid).outputs moved = [] := by
  change d.outputs moved = []
  exact List.eq_nil_of_length_eq_zero (by simp [Diagram.outputs, s.no_outputs])

theorem incoming_attached {w : Fin W} (port : w ∈ c.tied.inputs other) :
    c.tied.x w (d.vertexHeight other) = d.vertexX other := by
  have h := c.tied.finish_attached w other ((c.tied.input_exact other w).mpr (List.mem_ofFn.mp port))
  rw [show c.tied.vertexHeight other = d.vertexHeight other from height_other c _] at h
  exact h

theorem outgoing_attached {w : Fin W} (port : w ∈ c.tied.outputs other) :
    c.tied.x w (d.vertexHeight other) = d.vertexX other := by
  have h := c.tied.start_attached w other ((c.tied.output_exact other w).mpr (List.mem_ofFn.mp port))
  rw [show c.tied.vertexHeight other = d.vertexHeight other from height_other c _] at h
  exact h

theorem input_form :
    p.inputWires = p.left ++ (p.middle ++ c.tied.inputs other ++ p.right) := by
  simp only [PairSlice.inputWires, show c.tied.inputs moved = [] from no_inputs (s := s) _,
    List.nil_append, List.append_assoc]

theorem output_form :
    p.outputWires = p.left ++ (p.middle ++ c.tied.outputs other ++ p.right) := by
  simp only [PairSlice.outputWires, show c.tied.outputs moved = [] from no_outputs (s := s) _,
    List.nil_append, List.append_assoc]

private theorem vertex_x (j : Fin V) : c.tied.vertexX j = d.vertexX j := rfl

private theorem moved_center :
    c.tied.vertexHeight moved = d.vertexHeight other := s.moved_height _

/-- At the scalar event the unchanged order is a prefix before the scalar and
a suffix containing the stationary vertex's current port block. -/
theorem scalar_partition {y : ℝ} (band : y ∈ Set.Icc s.bottom s.top) {ports : List (Fin W)}
    (cut : c.tied.OrderedCut y (p.left ++ (p.middle ++ ports ++ p.right)))
    (attached : ∀ w ∈ ports, c.tied.x w (d.vertexHeight other) = d.vertexX other) (w : Fin W) :
    (w ∈ p.left ↔ c.tied.crosses w y ∧ c.tied.x w y < d.vertexX moved) ∧
    (w ∈ p.middle ++ ports ++ p.right ↔ c.tied.crosses w y ∧ d.vertexX moved < c.tied.x w y) := by
  let suffix := p.middle ++ ports ++ p.right
  have leftCenter (hw : w ∈ p.left) : c.tied.x w (d.vertexHeight other) < d.vertexX moved := by
    simpa only [moved_center c, vertex_x c] using ((p.left_exact w).mp hw).2
  have rightCenter (hw : w ∈ suffix) : d.vertexX moved < c.tied.x w (d.vertexHeight other) := by
    simp only [suffix, List.mem_append] at hw
    rcases hw with (hm | hp) | hr
    · simpa only [moved_center c, vertex_x c] using ((p.middle_exact w).mp hm).2.1
    · rw [attached w hp]
      exact c.horizontal
    · exact c.horizontal.trans (by simpa only [moved_center c, vertex_x c] using ((p.right_exact w).mp hr).2)
  have activeLeft (hw : w ∈ p.left) : c.tied.crosses w y :=
    (cut.exact_wires w).mp (List.mem_append.mpr (Or.inl hw))
  have activeRight (hw : w ∈ suffix) : c.tied.crosses w y :=
    (cut.exact_wires w).mp (List.mem_append.mpr (Or.inr hw))
  constructor
  · refine ⟨fun hw => ⟨activeLeft hw, (side_stable c band (activeLeft hw)).1.mpr (leftCenter hw)⟩, ?_⟩
    rintro ⟨active, side⟩
    rcases List.mem_append.mp ((cut.exact_wires w).mpr active) with hw | hw
    · exact hw
    · exact (lt_asymm ((side_stable c band active).1.mp side) (rightCenter hw)).elim
  · refine ⟨fun hw => ⟨activeRight hw, (side_stable c band (activeRight hw)).2.mpr (rightCenter hw)⟩, ?_⟩
    rintro ⟨active, side⟩
    rcases List.mem_append.mp ((cut.exact_wires w).mpr active) with hw | hw
    · exact (lt_asymm (leftCenter hw) ((side_stable c band active).2.mp side)).elim
    · exact hw

/-- At the stationary vertex the scalar contributes no wire to either block. -/
theorem stationary_partition (w : Fin W) :
    (w ∈ p.left ++ p.middle ↔ c.tied.crosses w (d.vertexHeight other) ∧
      c.tied.x w (d.vertexHeight other) < d.vertexX other) ∧
    (w ∈ p.right ↔ c.tied.crosses w (d.vertexHeight other) ∧ d.vertexX other < c.tied.x w (d.vertexHeight other)) := by
  have left := p.left_exact w
  have middle := p.middle_exact w
  have right := p.right_exact w
  simp only [moved_center c, vertex_x c] at left middle right
  refine ⟨?_, right⟩
  rw [List.mem_append, left, middle]
  constructor
  · rintro (⟨active, side⟩ | ⟨active, _, side⟩)
    · exact ⟨active, side.trans c.horizontal⟩
    · exact ⟨active, side⟩
  · rintro ⟨active, side⟩
    refine (lt_or_gt_of_ne ?_).elim (fun lt => Or.inl ⟨active, lt⟩)
      (fun gt => Or.inr ⟨active, gt, side⟩)
    have h : d.covers w (d.vertexHeight other) := by
      have original : d.crosses w (d.vertexHeight other) := by
        simpa only [Diagram.crosses, tied_lower c, tied_upper c] using active
      exact ⟨original.1.le, original.2.le⟩
    exact s.wire_clear w _ ⟨(c.bottom_early.trans c.early_other).le, (c.other_late.trans c.late_top).le⟩ h

end Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing
