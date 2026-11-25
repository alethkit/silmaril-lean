module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms
import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Thms
import Silmaril.Semantics.RuntimeWires.ProgressiveCutChoice.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGraph.Regression

open Silmaril.RuntimeWires.ProgressiveGraph

private abbrev signature : Signature Bool where
  Edge := Fin 3
  source v := if v = 2 then [true] else []
  target v := if v = 0 then [true] else []

private noncomputable def vertexHeight (v : Fin 3) : ℝ :=
  if v = 0 then 1 / 4 else if v = 1 then 1 / 2 else 3 / 4

private noncomputable def vertexX (v : Fin 3) : ℝ :=
  if v = 0 then 1 / 2 else if v = 1 then 3 / 4 else 5 / 8

private def start (w : Fin 2) : Option (Fin 3) := if w = 0 then none else some 0

private def finish (w : Fin 2) : Option (Fin 3) := if w = 0 then none else some 2

private noncomputable def horiz (w : Fin 2) (y : ℝ) : ℝ :=
  if w = 0 then (1 + y) / 8 else (7 + 4 * y) / 16

private noncomputable def exampleWire (w : Fin 2) :
    Wire (endpointHeight vertexHeight 0 (start w)) (endpointHeight vertexHeight 1 (finish w)) where
  x := horiz w
  increasing := by fin_cases w <;> norm_num [start, finish, vertexHeight, endpointHeight]
  continuous := by
    unfold horiz
    split <;> exact (by fun_prop : Continuous _).continuousOn
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold horiz
    split <;> ring

/-- A slanted boundary-to-boundary wire passes a creation, a scalar, and
a deletion. The other slanted wire goes directly from creation to deletion. -/
private noncomputable def drawing : Diagram signature 3 2 where
  vertexX := vertexX
  vertexHeight := vertexHeight
  vertex_inside := by
    intro v
    fin_cases v <;> norm_num [vertexX, vertexHeight, Set.mem_Ioo]
  vertex_separation := by
    intro v z hz
    fin_cases v <;> fin_cases z <;> norm_num [vertexHeight] at *
  generator := id
  label := fun i => decide (i ≠ 0)
  start := start
  finish := finish
  wire := exampleWire
  wire_inside := by
    intro w y hy
    fin_cases w <;>
      norm_num [exampleWire, horiz, start, finish, vertexHeight, endpointHeight,
        Set.mem_Icc, Set.mem_Ioo] at * <;>
      constructor <;> linarith [hy.1, hy.2]
  start_attached := by
    intro w v he
    fin_cases w <;> fin_cases v <;>
      norm_num [start, vertexHeight, vertexX, exampleWire, horiz] at *
  finish_attached := by
    intro w v he
    fin_cases w <;> fin_cases v <;>
      norm_num [finish, vertexHeight, vertexX, exampleWire, horiz] at *
  separated := by
    intro w z hw y ha hb
    fin_cases w <;> fin_cases z
    all_goals
      norm_num [exampleWire, horiz, start, finish, vertexHeight, endpointHeight,
        Set.mem_Icc, Set.mem_Ioo] at *
    all_goals
      intro he
      linarith [ha.1, hb.1]
  avoids_vertex := by
    intro w v h
    fin_cases w <;> fin_cases v <;>
      norm_num [exampleWire, horiz, vertexX, vertexHeight, start, finish, endpointHeight,
        Set.mem_Ioo] at *
  input_boundary_separated := by
    intro w z h he hf
    fin_cases w <;> fin_cases z <;> norm_num [start] at *
  output_boundary_separated := by
    intro w z h he hf
    fin_cases w <;> fin_cases z <;> norm_num [finish] at *
  input := fun _ _ => 1
  output := fun _ _ => 1
  input_exact := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [signature, finish]
  output_exact := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [signature, start]
  input_types := by
    intro v
    fin_cases v <;> simp [List.ofFn_succ]
  output_types := by
    intro v
    fin_cases v <;> simp [List.ofFn_succ]
  input_order := by
    intro v i j hij
    have small : (signature.source (id v)).length ≤ 1 := by fin_cases v <;> decide
    omega
  output_order := by
    intro v i j hij
    have small : (signature.target (id v)).length ≤ 1 := by fin_cases v <;> decide
    omega

private theorem first : drawing.Isolates 0 (1 / 8) (3 / 8) := by
  refine ⟨by norm_num, by norm_num [drawing, vertexHeight], by norm_num [drawing, vertexHeight],
    by norm_num, ?_⟩
  intro z hz
  fin_cases z <;> norm_num [drawing, vertexHeight, Set.mem_Icc] at *

private theorem middle : drawing.Isolates 1 (3 / 8) (5 / 8) := by
  refine ⟨by norm_num, by norm_num [drawing, vertexHeight], by norm_num [drawing, vertexHeight],
    by norm_num, ?_⟩
  intro z hz
  fin_cases z <;> norm_num [drawing, vertexHeight, Set.mem_Icc] at *

private theorem last : drawing.Isolates 2 (5 / 8) (7 / 8) := by
  refine ⟨by norm_num, by norm_num [drawing, vertexHeight], by norm_num [drawing, vertexHeight],
    by norm_num, ?_⟩
  intro z hz
  fin_cases z <;> norm_num [drawing, vertexHeight, Set.mem_Icc] at *

private noncomputable def creation := Classical.choice (Diagram.single_event first)

private noncomputable def scalar := Classical.choice (Diagram.single_event middle)

private noncomputable def deletion := Classical.choice (Diagram.single_event last)

private theorem shared_cut : drawing.OrderedCut (3 / 8) [0, 1] := by
  constructor
  · intro w
    fin_cases w <;> norm_num [drawing, Diagram.crosses, Diagram.lower, Diagram.upper, start,
      finish, endpointHeight, vertexHeight, Set.mem_Ioo]
  · rw [List.pairwise_pair]
    change (1 + 3 / 8 : ℝ) / 8 < (7 + 4 * (3 / 8)) / 16
    norm_num

/-- The first shared seam has exactly the two computed intersection points. -/
example :
    drawing.wireTrace ∩ {p | p.2 = (3 / 8 : ℝ)} =
      {p | p.2 = (3 / 8 : ℝ) ∧ p.1 ∈ ([11 / 64, 17 / 32] : List ℝ)} := by
  have reg : drawing.Regular (3 / 8) := by
    refine ⟨by norm_num [Set.mem_Ioo], ?_⟩
    intro v
    fin_cases v <;> norm_num [drawing, vertexHeight]
  rw [Diagram.regular_trace reg shared_cut]
  have positions : [0, 1].map (fun w => drawing.x w (3 / 8)) = [11 / 64, 17 / 32] := by
    change [(1 + 3 / 8 : ℝ) / 8, (7 + 4 * (3 / 8)) / 16] = _
    norm_num
  rw [positions]

/-- The slanted internal wire keeps its name and order through the isolated vertex. -/
example : creation.afterWires = [0, 1] ∧ scalar.beforeWires = scalar.afterWires := by
  refine ⟨Diagram.ordered_cut_unique creation.after shared_cut, ?_⟩
  have hin : drawing.inputs 1 = [] := rfl
  have hout : drawing.outputs 1 = [] := rfl
  simp [Diagram.EventSlice.beforeWires, Diagram.EventSlice.afterWires, hin, hout]

/-- Read the three geometric events as one typed sheet. -/
noncomputable example :
    Sliced.Sheet signature (creation.beforeWires.map drawing.label) (deletion.afterWires.map drawing.label) :=
  creation.prependAtSeam scalar (scalar.prependAtSeam deletion (deletion.prepend (.empty _)))

private theorem vertex_order : drawing.vertexOrder = Equiv.refl (Fin 3) := by
  unfold Diagram.vertexOrder
  apply Tuple.sort_eq_refl_iff_monotone.mpr
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [drawing, vertexHeight] at *

/-- The sweep finds the midpoint between creation and the isolated scalar. -/
example : drawing.cutHeight 1 = (3 / 8 : ℝ) := by
  simp only [Diagram.cutHeight, Diagram.landmark, vertex_order]
  change (drawing.vertexHeight 0 + drawing.vertexHeight 1) / 2 = _
  norm_num [drawing, vertexHeight]

/-- Read back the original internal wire and the boundary-to-boundary wire. -/
example :
    drawing.sweep.readStart 1 = some 0 ∧
    drawing.sweep.readFinish 1 = some 2 ∧
    drawing.sweep.readStart 0 = none ∧
    drawing.sweep.readFinish 0 = none := by
  simp [Diagram.Sweep.readStart_eq, Diagram.Sweep.readFinish_eq, drawing, start, finish]

/-- The internal wire appears at exactly the two cuts on either side of the scalar. -/
example : drawing.sweep.wireCuts 1 = {1, 2} := by
  ext i
  simp only [Diagram.Sweep.wireCuts, Finset.mem_filter, Finset.mem_univ, true_and,
    Diagram.Sweep.wire_span]
  have startRank : (drawing.startIndex 1).val = 1 := by
    rw [Diagram.startIndex, show drawing.start 1 = some 0 from rfl]
    change (drawing.vertexOrder.symm 0).val + 1 = 1
    rw [vertex_order]
    rfl
  have finishRank : (drawing.finishIndex 1).val = 3 := by
    rw [Diagram.finishIndex, show drawing.finish 1 = some 2 from rfl]
    change (drawing.vertexOrder.symm 2).val + 1 = 3
    rw [vertex_order]
    rfl
  rw [startRank, finishRank]
  fin_cases i <;> decide

/-- In the vertex-free case the schedule uses just the midpoint of the caps. -/
example (d : Diagram signature 0 2) : d.cutHeight 0 = (1 / 2 : ℝ) := by
  change ((0 : ℝ) + 1) / 2 = _
  norm_num

open Silmaril.RuntimeWires.Sliced

private theorem cap_singleton (i : Fin 4)
    (members : ∀ w : Fin 2, w ∈ drawing.sweep.wires i ↔ w = 0) :
    drawing.sweep.wires i = [0] := by
  have nd : (drawing.sweep.wires i).Nodup :=
    (drawing.sweep.ordered i).ordered.imp
      (fun h => ne_of_apply_ne (fun w => drawing.x w (drawing.sweep.cuts.height i)) (ne_of_lt h))
  exact ((List.perm_ext_iff_of_nodup nd (by simp)).mpr (by simpa using members)).eq_singleton

private theorem input_cap : drawing.sweep.wires 0 = [0] := by
  apply cap_singleton
  intro w
  rw [drawing.sweep.input_mem]
  fin_cases w <;> simp [drawing, start]

private theorem output_cap : drawing.sweep.wires (Fin.last 3) = [0] := by
  apply cap_singleton
  intro w
  rw [drawing.sweep.output_mem]
  fin_cases w <;> simp [drawing, finish]

/-- The decoder sees the same source-port name leaving creation and entering
deletion, preserves the boundary wire, and records the isolated scalar. -/
example :
    drawing.sweep.sheet.traceWires =
      ⟨[[⟨0, [], [(true, .box 0 0 0)]⟩],
        [⟨1, [], []⟩],
        [⟨2, [(true, .box 0 0 0)], []⟩]],
        [(false, .boundary 0)]⟩ := by
  have wire : drawing.sweep.namedWire 1 = (true, .box 0 0 0) := by
    rw [Diagram.Sweep.namedWire, Diagram.Sweep.origin, show drawing.start 1 = some 0 from rfl]
    rw [vertex_order]
    rfl
  have boundary : drawing.sweep.namedWire 0 = (false, .boundary 0) := by
    rw [Diagram.Sweep.namedWire, Diagram.Sweep.origin, show drawing.start 0 = none from rfl, input_cap]
    rfl
  rw [drawing.sweep.trace_sheet, Diagram.Sweep.expectedTrace, output_cap]
  have create : drawing.sweep.expectedBox 0 = ⟨0, [], [(true, .box 0 0 0)]⟩ := by
    rw [Diagram.Sweep.expectedBox, vertex_order]
    change (⟨0, [], [drawing.sweep.namedWire 1]⟩ : BoxTrace signature) = _
    rw [wire]
  have scalar : drawing.sweep.expectedBox 1 = ⟨1, [], []⟩ := by
    rw [Diagram.Sweep.expectedBox, vertex_order]
    rfl
  have delete : drawing.sweep.expectedBox 2 = ⟨2, [(true, .box 0 0 0)], []⟩ := by
    rw [Diagram.Sweep.expectedBox, vertex_order]
    change (⟨2, [drawing.sweep.namedWire 1], []⟩ : BoxTrace signature) = _
    rw [wire]
  change (⟨[[drawing.sweep.expectedBox 0], [drawing.sweep.expectedBox 1], [drawing.sweep.expectedBox 2]],
    [drawing.sweep.namedWire 0]⟩ : SheetTrace signature) = _
  rw [create, scalar, delete, boundary]

example (d : Diagram signature 0 2) :
    d.sweep.sheet.traceWires = ⟨[], namePorts .boundary ((d.sweep.wires 0).map d.label)⟩ :=
  d.sweep.trace_no_vertices

/-- Even equal labels at the boundary have distinct source-port names. -/
example :
    (Sliced.Sheet.empty (S := signature) [true, true]).traceWires =
      ⟨[], [(true, .boundary 0), (true, .boundary 1)]⟩ :=
  rfl

private theorem landmark_coordinates (i : Fin 5) : drawing.landmark i = (i.val : ℝ) / 4 := by
  unfold Diagram.landmark
  rw [vertex_order]
  fin_cases i
  · change (0 : ℝ) = _
    norm_num
  · change vertexHeight 0 = _
    norm_num [vertexHeight]
  · change vertexHeight 1 = _
    norm_num [vertexHeight]
  · change vertexHeight 2 = _
    norm_num [vertexHeight]
  · change (1 : ℝ) = _
    norm_num

/-- Shift every midpoint cut toward the preceding landmark. -/
private noncomputable def alternateCuts : drawing.Cuts where
  height i := (4 * (i.val : ℝ) + 1) / 16
  in_gap := by
    intro i
    fin_cases i <;> norm_num [Diagram.gap, landmark_coordinates, Set.mem_Ioo]

/-- Every alternate height differs from its midpoint, including the gaps
next to the two caps. -/
example (i : Fin 4) : alternateCuts.height i ≠ drawing.cutHeight i := by
  fin_cases i <;> norm_num [alternateCuts, Diagram.cutHeight, landmark_coordinates]

/-- The cut moves from height 3/8 to 5/16 and still reads the same two slanted wires. -/
example :
    alternateCuts.height 1 = (5 / 16 : ℝ) ∧ (drawing.sweepAt alternateCuts).wires 1 = [0, 1] := by
  refine ⟨by norm_num [alternateCuts], ?_⟩
  have midpoint : (3 / 8 : ℝ) ∈ drawing.gap 1 := by
    norm_num [Diagram.gap, landmark_coordinates, Set.mem_Ioo]
  have relocated := shared_cut.relocate midpoint (alternateCuts.in_gap 1)
  have read := (drawing.sweepAt alternateCuts).ordered 1
  rw [Diagram.sweepAt_cuts] at read
  exact Diagram.ordered_cut_unique read relocated

/-- The whole alternate sheet agrees with the midpoint sheet after the two
boundary transports. This includes the isolated nullary generator. -/
example :
    let alt := drawing.sweepAt alternateCuts
    let mid := drawing.sweep
    (congrArg₂ (Sliced.Sheet signature)
      (congrArg (List.map drawing.label) (alt.wires_eq mid 0))
      (congrArg (List.map drawing.label) (alt.wires_eq mid (Fin.last 3)))).mp alt.sheet = mid.sheet :=
  (drawing.sweepAt alternateCuts).sheet_eq drawing.sweep

end Silmaril.RuntimeWires.Proofs.ProgressiveGraph.Regression
