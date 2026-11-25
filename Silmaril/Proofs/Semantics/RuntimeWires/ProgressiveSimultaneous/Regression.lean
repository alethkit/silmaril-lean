module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSimultaneous.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous.Regression

open Silmaril.RuntimeWires.ProgressiveGraph Silmaril.RuntimeWires.Sliced

private abbrev signature : Signature Bool where
  Edge := Fin 2
  source v := if v = 0 then [] else [true]
  target v := if v = 0 then [] else [false]

private noncomputable def vertexX (v : Fin 2) : ℝ := if v = 0 then 1 / 4 else 3 / 4
private noncomputable def height (_ : Fin 2) : ℝ := 1 / 2
private def start (w : Fin 4) : Option (Fin 2) := if w = 3 then some 1 else none
private def finish (w : Fin 4) : Option (Fin 2) := if w = 2 then some 1 else none

private noncomputable def x (w : Fin 4) (y : ℝ) : ℝ :=
  if w = 0 then 1 / 8 else if w = 1 then (3 + y) / 8
    else if w = 2 then (7 - 2 * y) / 8 else (5 + 2 * y) / 8

private noncomputable def strand (w : Fin 4) :
    Wire (endpointHeight height 0 (start w)) (endpointHeight height 1 (finish w)) where
  x := x w
  increasing := by fin_cases w <;> norm_num [start, finish, height, endpointHeight]
  continuous := by
    unfold x
    split
    · exact continuous_const.continuousOn
    · split
      · exact (by fun_prop : Continuous _).continuousOn
      · split <;> exact (by fun_prop : Continuous _).continuousOn
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold x
    split
    · ring
    · split
      · ring
      · split <;> ring

/-- A scalar and a unary generator lie at equal heights. One passing wire
is to the left of both, and a second passing wire lies between their slots. -/
private noncomputable def drawing : Diagram signature 2 4 .point where
  vertexX := vertexX
  vertexHeight := height
  vertex_inside := by intro v; fin_cases v <;> norm_num [vertexX, height, Set.mem_Ioo]
  vertex_separation := by
    intro i j he
    have hx := congrArg Prod.fst he
    fin_cases i <;> fin_cases j <;> norm_num [vertexX] at *
  generator := id
  label := fun i => decide (i = 2)
  start := start
  finish := finish
  wire := strand
  wire_inside := by
    intro w y hy
    fin_cases w <;> norm_num [strand, x, start, finish, height, endpointHeight,
      Set.mem_Icc, Set.mem_Ioo] at * <;>
      constructor <;> linarith [hy.1, hy.2]
  start_attached := by
    intro w v he
    fin_cases w <;> fin_cases v <;> norm_num [start, height, vertexX, strand, x] at *
  finish_attached := by
    intro w v he
    fin_cases w <;> fin_cases v <;> norm_num [finish, height, vertexX, strand, x] at *
  separated := by
    intro w z hw y ha hb
    fin_cases w <;> fin_cases z
    all_goals
      norm_num [strand, x, start, finish, height, endpointHeight, Set.mem_Icc, Set.mem_Ioo] at *
    all_goals
      intro he
      linarith [ha.1, ha.2, hb.1, hb.2]
  avoids_vertex := by
    intro w v hw
    fin_cases w <;> fin_cases v <;>
      norm_num [strand, x, vertexX, height, start, finish, endpointHeight, Set.mem_Ioo] at *
  input_boundary_separated := by
    intro w z hw hs ht
    fin_cases w <;> fin_cases z <;> norm_num [start, strand, x] at *
  output_boundary_separated := by
    intro w z hw hs ht
    fin_cases w <;> fin_cases z <;> norm_num [finish, strand, x] at *
  input := fun _ _ => 2
  output := fun _ _ => 3
  input_exact := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [signature, finish]
  output_exact := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [signature, start]
  input_types := by intro v; fin_cases v <;> simp [List.ofFn_succ]
  output_types := by intro v; fin_cases v <;> simp [List.ofFn_succ]
  input_order := by
    intro v i j hij
    have small : (signature.source (id v)).length ≤ 1 := by fin_cases v <;> decide
    omega
  output_order := by
    intro v i j hij
    have small : (signature.target (id v)).length ≤ 1 := by fin_cases v <;> decide
    omega

private theorem wire_position (w : Fin 4) (y : ℝ) : (drawing.wire w).x y = x w y := rfl

private theorem isolated : drawing.IsolatesPair 0 1 (1 / 4) (3 / 4) := by
  refine ⟨rfl, ?_, by norm_num, ?_, ?_, by norm_num, ?_⟩
  · norm_num [drawing, vertexX]
  · norm_num [drawing, height]
  · norm_num [drawing, height]
  · intro j h
    fin_cases j <;> simp

private noncomputable def slice := Classical.choice (Diagram.simultaneous_event isolated)

private theorem known_input : drawing.OrderedCut (1 / 4) [0, 1, 2] := by
  constructor
  · intro w
    fin_cases w <;> norm_num [drawing, Diagram.crosses, Diagram.lower, Diagram.upper, start,
      finish, endpointHeight, height, Set.mem_Ioo]
  · norm_num [Diagram.x, wire_position, x]

private theorem known_output : drawing.OrderedCut (3 / 4) [0, 1, 3] := by
  constructor
  · intro w
    fin_cases w <;> norm_num [drawing, Diagram.crosses, Diagram.lower, Diagram.upper, start,
      finish, endpointHeight, height, Set.mem_Ioo]
  · norm_num [Diagram.x, wire_position, x]

/-- Both outer cuts recover the exact ID lists. The scalar has no ports,
but its slot lies strictly between the first and second passing wires. -/
example :
    slice.inputWires = [0, 1, 2] ∧ slice.outputWires = [0, 1, 3] ∧
    drawing.inputs 0 = [] ∧ drawing.outputs 0 = [] ∧ 0 ∈ slice.left ∧ 1 ∈ slice.middle := by
  refine ⟨Diagram.ordered_cut_unique slice.before known_input,
    Diagram.ordered_cut_unique slice.after known_output, rfl, rfl, ?_, ?_⟩
  · rw [slice.left_exact]
    simp only [Diagram.x, wire_position]
    norm_num [drawing, Diagram.crosses, Diagram.lower, Diagram.upper, start,
      finish, endpointHeight, height, x, vertexX, Set.mem_Ioo]
  · rw [slice.middle_exact]
    simp only [Diagram.x, wire_position]
    norm_num [drawing, Diagram.crosses, Diagram.lower, Diagram.upper, start,
      finish, endpointHeight, height, x, vertexX, Set.mem_Ioo]

example : Sheet.SeamEquivalent slice.leftFirst slice.rightFirst :=
  slice.serialization_eq

end Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous.Regression
