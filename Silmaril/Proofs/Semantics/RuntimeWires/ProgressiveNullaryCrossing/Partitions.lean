module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Geometry

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : Diagram S V W .point} {moved other : Fin V} {s : d.NullarySlide moved}
variable {side : NullarySlide.Side} (c : s.Crossing other side)
variable (p : c.tied.PairSlice (side.leftVertex moved other) (side.rightVertex moved other) c.lowerCut c.upperCut)

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

/-- At the scalar event the stationary vertex contributes its current ports
on the opposite side, in their original port order. -/
def scalarLeft (ports : List (Fin W)) : List (Fin W) :=
  match side with
  | .left => p.left
  | .right => p.left ++ (ports ++ p.middle)

def scalarRight (ports : List (Fin W)) : List (Fin W) :=
  match side with
  | .left => p.middle ++ (ports ++ p.right)
  | .right => p.right

/-- At the stationary event the scalar contributes no wires. -/
def stationaryLeft : List (Fin W) :=
  match side with
  | .left => p.left ++ p.middle
  | .right => p.left

def stationaryRight : List (Fin W) :=
  match side with
  | .left => p.right
  | .right => p.middle ++ p.right

theorem input_form :
    p.inputWires = scalarLeft c p (c.tied.inputs other) ++ scalarRight c p (c.tied.inputs other) := by
  have empty : c.tied.inputs moved = [] := no_inputs (s := s) _
  cases side <;> simp only [PairSlice.inputWires, scalarLeft, scalarRight, NullarySlide.Side.leftVertex,
    NullarySlide.Side.rightVertex, empty, List.nil_append, List.append_assoc]

theorem output_form :
    p.outputWires = scalarLeft c p (c.tied.outputs other) ++ scalarRight c p (c.tied.outputs other) := by
  have empty : c.tied.outputs moved = [] := no_outputs (s := s) _
  cases side <;> simp only [PairSlice.outputWires, scalarLeft, scalarRight, NullarySlide.Side.leftVertex,
    NullarySlide.Side.rightVertex, empty, List.nil_append, List.append_assoc]

theorem stationary_input_form :
    p.inputWires = (stationaryLeft c p ++ c.tied.inputs other) ++ stationaryRight c p := by
  rw [input_form c p]
  cases side <;> simp [scalarLeft, scalarRight, stationaryLeft, stationaryRight, List.append_assoc]

theorem stationary_output_form :
    p.outputWires = (stationaryLeft c p ++ c.tied.outputs other) ++ stationaryRight c p := by
  rw [output_form c p]
  cases side <;> simp [scalarLeft, scalarRight, stationaryLeft, stationaryRight, List.append_assoc]

private theorem vertex_x (j : Fin V) : c.tied.vertexX j = d.vertexX j := rfl

private theorem left_center (w : Fin W) :
    w ∈ p.left ↔ c.tied.crosses w (d.vertexHeight other) ∧
      c.tied.x w (d.vertexHeight other) < d.vertexX (side.leftVertex moved other) := by
  simpa only [center_height_left c, vertex_x c] using p.left_exact w

private theorem middle_center (w : Fin W) :
    w ∈ p.middle ↔ c.tied.crosses w (d.vertexHeight other) ∧
      d.vertexX (side.leftVertex moved other) < c.tied.x w (d.vertexHeight other) ∧
      c.tied.x w (d.vertexHeight other) < d.vertexX (side.rightVertex moved other) := by
  simpa only [center_height_left c, vertex_x c] using p.middle_exact w

private theorem right_center (w : Fin W) :
    w ∈ p.right ↔ c.tied.crosses w (d.vertexHeight other) ∧
      d.vertexX (side.rightVertex moved other) < c.tied.x w (d.vertexHeight other) := by
  simpa only [center_height_left c, vertex_x c] using p.right_exact w

private theorem scalar_left_center {w : Fin W} {ports : List (Fin W)}
    (attached : ∀ w ∈ ports, c.tied.x w (d.vertexHeight other) = d.vertexX other)
    (hw : w ∈ scalarLeft c p ports) : c.tied.x w (d.vertexHeight other) < d.vertexX moved := by
  cases side
  · exact ((left_center c p w).mp hw).2
  · simp only [scalarLeft, List.mem_append] at hw
    rcases hw with left | port | middle
    · exact ((left_center c p w).mp left).2.trans c.horizontal
    · rw [attached w port]
      exact c.horizontal
    · exact ((middle_center c p w).mp middle).2.2

private theorem scalar_right_center {w : Fin W} {ports : List (Fin W)}
    (attached : ∀ w ∈ ports, c.tied.x w (d.vertexHeight other) = d.vertexX other)
    (hw : w ∈ scalarRight c p ports) : d.vertexX moved < c.tied.x w (d.vertexHeight other) := by
  cases side
  · simp only [scalarRight, List.mem_append] at hw
    rcases hw with middle | port | right
    · exact ((middle_center c p w).mp middle).2.1
    · rw [attached w port]
      exact c.horizontal
    · exact c.horizontal.trans ((right_center c p w).mp right).2
  · exact ((right_center c p w).mp hw).2

/-- The wire-free path transports the side of every active strand at the scalar event. -/
theorem scalar_partition {y : ℝ} (band : y ∈ Set.Icc s.bottom s.top) {ports : List (Fin W)}
    (cut : c.tied.OrderedCut y (scalarLeft c p ports ++ scalarRight c p ports))
    (attached : ∀ w ∈ ports, c.tied.x w (d.vertexHeight other) = d.vertexX other) (w : Fin W) :
    (w ∈ scalarLeft c p ports ↔ c.tied.crosses w y ∧ c.tied.x w y < d.vertexX moved) ∧
    (w ∈ scalarRight c p ports ↔ c.tied.crosses w y ∧ d.vertexX moved < c.tied.x w y) := by
  have activeLeft (hw : w ∈ scalarLeft c p ports) : c.tied.crosses w y :=
    (cut.exact_wires w).mp (List.mem_append.mpr (Or.inl hw))
  have activeRight (hw : w ∈ scalarRight c p ports) : c.tied.crosses w y :=
    (cut.exact_wires w).mp (List.mem_append.mpr (Or.inr hw))
  have leftCenter := scalar_left_center c p attached (w := w)
  have rightCenter := scalar_right_center c p attached (w := w)
  constructor
  · refine ⟨fun hw => ⟨activeLeft hw, (side_stable c band (activeLeft hw)).1.mpr (leftCenter hw)⟩, ?_⟩
    rintro ⟨active, sign⟩
    rcases List.mem_append.mp ((cut.exact_wires w).mpr active) with hw | hw
    · exact hw
    · exact (lt_asymm ((side_stable c band active).1.mp sign) (rightCenter hw)).elim
  · refine ⟨fun hw => ⟨activeRight hw, (side_stable c band (activeRight hw)).2.mpr (rightCenter hw)⟩, ?_⟩
    rintro ⟨active, sign⟩
    rcases List.mem_append.mp ((cut.exact_wires w).mpr active) with hw | hw
    · exact (lt_asymm (leftCenter hw) ((side_stable c band active).2.mp sign)).elim
    · exact hw

/-- At the stationary vertex, the through block between the vertices joins
the exterior block on the same side of the stationary vertex. -/
theorem stationary_partition (w : Fin W) :
    (w ∈ stationaryLeft c p ↔ c.tied.crosses w (d.vertexHeight other) ∧
      c.tied.x w (d.vertexHeight other) < d.vertexX other) ∧
    (w ∈ stationaryRight c p ↔ c.tied.crosses w (d.vertexHeight other) ∧
      d.vertexX other < c.tied.x w (d.vertexHeight other)) := by
  have avoids (active : c.tied.crosses w (d.vertexHeight other)) :
      c.tied.x w (d.vertexHeight other) ≠ d.vertexX moved := by
    have original : d.crosses w (d.vertexHeight other) := by
      simpa only [Diagram.crosses, tied_lower c, tied_upper c] using active
    exact s.wire_clear w _ ⟨(c.bottom_early.trans c.early_other).le, (c.other_late.trans c.late_top).le⟩
      ⟨original.1.le, original.2.le⟩
  have left := left_center c p w
  have middle := middle_center c p w
  have right := right_center c p w
  cases side
  · refine ⟨?_, right⟩
    rw [stationaryLeft, List.mem_append, left, middle]
    constructor
    · rintro (⟨active, sign⟩ | ⟨active, _, sign⟩)
      · exact ⟨active, sign.trans c.horizontal⟩
      · exact ⟨active, sign⟩
    · rintro ⟨active, sign⟩
      exact (lt_or_gt_of_ne (avoids active)).elim (fun lt => Or.inl ⟨active, lt⟩)
        (fun gt => Or.inr ⟨active, gt, sign⟩)
  · refine ⟨left, ?_⟩
    rw [stationaryRight, List.mem_append, middle, right]
    constructor
    · rintro (⟨active, sign, _⟩ | ⟨active, sign⟩)
      · exact ⟨active, sign⟩
      · exact ⟨active, c.horizontal.trans sign⟩
    · rintro ⟨active, sign⟩
      exact (lt_or_gt_of_ne (avoids active)).elim (fun lt => Or.inl ⟨active, sign, lt⟩)
        (fun gt => Or.inr ⟨active, gt⟩)

end Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing
