module

public import Silmaril.Semantics.RuntimeWires.ProgressiveStripSwap.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveStripSwap.Regression

open ProgressiveGraph

private def signature : Signature (Fin 3) where
  Edge := Fin 2
  source e := [if e.val = 0 then 0 else 2]
  target e := [if e.val = 0 then 0 else 2]

private def center (j : Fin 2) : ℝ := if j.val = 0 then 1 / 4 else 3 / 4
private def altitude (j : Fin 2) : ℝ := if j.val = 0 then 1 / 3 else 2 / 3
private def start (w : Fin 5) : Option (Fin 2) :=
  if w.val = 1 then some 0 else if w.val = 4 then some 1 else none
private def finish (w : Fin 5) : Option (Fin 2) :=
  if w.val = 0 then some 0 else if w.val = 3 then some 1 else none
private def label (w : Fin 5) : Fin 3 := if w.val < 2 then 0 else if w.val = 2 then 1 else 2
private def track (w : Fin 5) (y : ℝ) : ℝ :=
  if w.val < 2 then 1 / 4 + (y - 1 / 3) / 40
  else if w.val = 2 then 1 / 2 else 3 / 4 + (y - 2 / 3) / 40

private def wire (w : Fin 5) : Wire (endpointHeight altitude 0 (start w)) (endpointHeight altitude 1 (finish w)) where
  x := track w
  increasing := by fin_cases w <;> norm_num [start, finish, altitude, endpointHeight]
  continuous := by unfold track; split <;> first | fun_prop | (split <;> fun_prop)
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    fin_cases w <;> norm_num [track] <;> ring

private def incoming (j : Fin 2) : Fin 5 := if j.val = 0 then 0 else 3
private def outgoing (j : Fin 2) : Fin 5 := if j.val = 0 then 1 else 4

/-- The two unary vertices have slanted incident strands and a stationary
through-wire between their strips. -/
private def initial : ProgressiveGraph.Diagram signature 2 5 .point where
  vertexX := center
  vertexHeight := altitude
  vertex_inside j := by fin_cases j <;> norm_num [center, altitude, Set.mem_Ioo]
  vertex_separation := by
    intro i j same
    have xs := congrArg Prod.fst same
    fin_cases i <;> fin_cases j
    all_goals norm_num [center] at xs
    all_goals rfl
  generator := id
  label := label
  start := start
  finish := finish
  wire := wire
  wire_inside := by
    intro w y h
    fin_cases w <;> norm_num [wire, track, start, finish, altitude, endpointHeight, Set.mem_Icc, Set.mem_Ioo] at *
    all_goals constructor <;> linarith [h.1, h.2]
  start_attached := by
    intro w j h
    fin_cases w <;> fin_cases j
    all_goals norm_num [start] at h
    all_goals norm_num [wire, track, altitude, center]
  finish_attached := by
    intro w j h
    fin_cases w <;> fin_cases j
    all_goals norm_num [finish] at h
    all_goals norm_num [wire, track, altitude, center]
  separated := by
    intro w z ne y inside covers eq
    fin_cases w <;> fin_cases z <;>
      norm_num [wire, start, finish, track, altitude, endpointHeight, Set.mem_Ioo, Set.mem_Icc] at *
    all_goals linarith [inside.1, inside.2, covers.1, covers.2]
  avoids_vertex := by
    intro w j inside eq
    fin_cases w <;> fin_cases j <;>
      norm_num [wire, start, finish, track, altitude, center, endpointHeight, Set.mem_Ioo] at *
  input_boundary_separated := by
    intro w z ne hw hz
    fin_cases w <;> fin_cases z <;> norm_num [wire, track, start] at *
  output_boundary_separated := by
    intro w z ne hw hz
    fin_cases w <;> fin_cases z <;> norm_num [wire, track, finish] at *
  input j _ := incoming j
  output j _ := outgoing j
  input_exact := by
    intro j w
    have nonempty : 0 < (signature.source j).length := by fin_cases j <;> decide
    have port : finish w = some j ↔ incoming j = w := by fin_cases j <;> fin_cases w <;> decide
    exact port.trans ⟨fun h => ⟨⟨0, nonempty⟩, h⟩, fun ⟨_, h⟩ => h⟩
  output_exact := by
    intro j w
    have nonempty : 0 < (signature.target j).length := by fin_cases j <;> decide
    have port : start w = some j ↔ outgoing j = w := by fin_cases j <;> fin_cases w <;> decide
    exact port.trans ⟨fun h => ⟨⟨0, nonempty⟩, h⟩, fun ⟨_, h⟩ => h⟩
  input_types j := by fin_cases j <;> rfl
  output_types j := by fin_cases j <;> rfl
  input_order := by
    intro j i k less
    change Fin 1 at i k
    exact (less.ne (Subsingleton.elim i k)).elim
  output_order := by
    intro j i k less
    change Fin 1 at i k
    exact (less.ne (Subsingleton.elim i k)).elim

private def strips : SwapStrips where
  left := ⟨1 / 8, 1 / 5, 3 / 10, 3 / 8, by norm_num, by norm_num, by norm_num, by norm_num⟩
  right := ⟨5 / 8, 7 / 10, 4 / 5, 7 / 8, by norm_num, by norm_num, by norm_num, by norm_num⟩
  ordered := by norm_num

private def swap : initial.IsolatedStripSwap where
  strips := strips
  left := 0
  right := 1
  ordered := by change (1 / 3 : ℝ) < 2 / 3; norm_num
  vertexRegion j := if j.val = 0 then .left else .right
  left_region := rfl
  right_region := rfl
  other_region := by intro j h k; fin_cases j <;> contradiction
  vertex_mem := by
    intro j
    fin_cases j <;> norm_num [initial, center, strips, SwapStrips.region, SwapStrip.core, Set.mem_Icc]
  wireRegion w := if w.val < 2 then .left else if w.val = 2 then .exterior else .right
  wire_mem := by
    intro w y covers
    change track w y ∈ strips.region (if w.val < 2 then .left else if w.val = 2 then .exterior else .right)
    change y ∈ Set.Icc (endpointHeight altitude 0 (start w)) (endpointHeight altitude 1 (finish w)) at covers
    fin_cases w <;>
      norm_num [track, start, finish, strips, SwapStrips.region, SwapStrip.core, SwapStrip.support,
        altitude, endpointHeight, Set.mem_Icc, Set.mem_Ioo, Set.mem_compl_iff, Set.mem_union] at *
    all_goals constructor <;> linarith [covers.1, covers.2]

private def midpoint : SlabIsotopy.Time := ⟨1 / 2, by norm_num [Set.mem_Icc]⟩
private def final : SlabIsotopy.Time := ⟨1, zero_le_one, le_rfl⟩

private theorem midpoint_heights : (swap.isotopy.drawing midpoint).vertexHeight 0 = 1 / 2 ∧
    (swap.isotopy.drawing midpoint).vertexHeight 1 = 1 / 2 := by
  have left := swap.left_height midpoint
  have right := swap.right_height midpoint
  change (swap.isotopy.drawing midpoint).vertexHeight 0 = interpolate (1 / 3) (2 / 3) (1 / 2) at left
  change (swap.isotopy.drawing midpoint).vertexHeight 1 = interpolate (2 / 3) (1 / 3) (1 / 2) at right
  norm_num [interpolate] at left right
  exact ⟨left, right⟩

example : (swap.isotopy.drawing midpoint).vertexX 0 ≠ (swap.isotopy.drawing midpoint).vertexX 1 := by
  intro same
  have equal : (0 : Fin 2) = 1 := (swap.isotopy.drawing midpoint).vertex_separation
    (Prod.ext same (midpoint_heights.1.trans midpoint_heights.2.symm))
  exact (by decide : (0 : Fin 2) ≠ 1) equal

example : (swap.isotopy.drawing final).vertexHeight 1 < (swap.isotopy.drawing final).vertexHeight 0 := by
  obtain ⟨left, right⟩ := swap.final_height
  change (swap.isotopy.drawing final).vertexHeight 0 = 2 / 3 at left
  change (swap.isotopy.drawing final).vertexHeight 1 = 1 / 3 at right
  rw [left, right]
  norm_num

example (t : SlabIsotopy.Time) : ((swap.isotopy.drawing t).wire 2).trace = (initial.wire 2).trace :=
  swap.exterior_trace t 2 rfl

example (t : SlabIsotopy.Time) : (swap.isotopy.drawing t).start (1 : Fin 5) = some 0 ∧
    (swap.isotopy.drawing t).finish (3 : Fin 5) = some 1 := by
  rw [swap.isotopy.start, swap.isotopy.finish]
  exact ⟨rfl, rfl⟩

example (t : SlabIsotopy.Time) : (swap.isotopy.drawing t).x 0 0 = initial.x 0 0 ∧
    (swap.isotopy.drawing t).x 4 1 = initial.x 4 1 :=
  ⟨swap.cap_x t 0 0 (Or.inl le_rfl), swap.cap_x t 4 1 (Or.inr le_rfl)⟩

end Silmaril.RuntimeWires.Proofs.ProgressiveStripSwap.Regression
