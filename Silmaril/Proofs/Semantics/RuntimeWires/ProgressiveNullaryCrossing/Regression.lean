module

public import Silmaril.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing.Regression

open ProgressiveGraph Sliced

private abbrev signature : Signature (Fin 2) where
  Edge := Fin 2
  source j := if j = 0 then [] else [0, 1]
  target _ := []

private noncomputable def vertexX (j : Fin 2) : ℝ := if j = 0 then 1 / 4 else 5 / 8
private noncomputable def height (_ : Fin 2) : ℝ := 1 / 2

private noncomputable def x (w : Fin 2) (y : ℝ) : ℝ :=
  if w = 0 then (2 + y) / 4 else (3 - y) / 4

private noncomputable def strand (w : Fin 2) : Wire 0 (1 / 2) where
  x := x w
  increasing := by norm_num
  continuous := by
    unfold x
    split <;> exact (by fun_prop : Continuous _).continuousOn
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold x
    split <;> ring

/-- Two slanted inputs meet at the stationary generator. Their order is a
geometric property throughout their common open height interval. -/
private noncomputable def drawing : ProgressiveGraph.Diagram signature 2 2 .point where
  vertexX := vertexX
  vertexHeight := height
  vertex_inside := by intro v; fin_cases v <;> norm_num [vertexX, height, Set.mem_Ioo]
  vertex_separation := by
    intro i j eq
    have hx := congrArg Prod.fst eq
    fin_cases i <;> fin_cases j <;> norm_num [vertexX] at *
  generator := id
  label := id
  start := fun _ => none
  finish := fun _ => some 1
  wire := strand
  wire_inside := by
    intro w y hy
    fin_cases w <;> norm_num [strand, x, height, endpointHeight, Set.mem_Icc, Set.mem_Ioo] at * <;>
      constructor <;> linarith [hy.1, hy.2]
  start_attached := by simp
  finish_attached := by
    intro w j eq
    have hj := (Option.some.inj eq).symm
    subst j
    fin_cases w <;> norm_num [strand, x, vertexX, height]
  separated := by
    intro w z different y active closed eq
    fin_cases w <;> fin_cases z <;>
      norm_num [strand, x, height, endpointHeight, Set.mem_Ioo, Set.mem_Icc] at *
    all_goals linarith [active.2]
  avoids_vertex := by
    intro w j active
    fin_cases j <;> norm_num [strand, x, height, endpointHeight, Set.mem_Ioo] at active
  input_boundary_separated := by
    intro w z different _ _
    fin_cases w <;> fin_cases z <;> norm_num [strand, x] at *
  output_boundary_separated := by simp
  input := fun j i => ⟨i.val, i.isLt.trans_le (by fin_cases j <;> decide)⟩
  output := fun j i => Fin.elim0 (show Fin 0 from i)
  input_exact := by
    intro j w
    fin_cases j
    · simp [signature]
    · refine ⟨fun _ => ⟨w, rfl⟩, fun _ => rfl⟩
  output_exact := by simp [signature]
  input_types := by
    intro j
    fin_cases j <;> simp [List.ofFn_succ]
  output_types := by simp [List.ofFn_zero]
  input_order := by
    intro j i k ordered y _ _ below
    fin_cases j
    · exact Fin.elim0 (show Fin 0 from i)
    · change (i : ℕ) < (k : ℕ) at ordered
      have boundI : (i : ℕ) < 2 := i.isLt
      have boundK : (k : ℕ) < 2 := k.isLt
      have left : (⟨i.val, boundI⟩ : Fin 2) = 0 := Fin.ext (by
        change i.val = 0
        omega)
      have right : (⟨k.val, boundK⟩ : Fin 2) = 1 := Fin.ext (by
        change k.val = 1
        omega)
      change x ⟨i.val, boundI⟩ y < x ⟨k.val, boundK⟩ y
      rw [left, right]
      norm_num [x]
      linarith [show y < 1 / 2 from below]
  output_order := fun _ {i} => Fin.elim0 (show Fin 0 from i)

private noncomputable def slide : drawing.NullarySlide 0 where
  bottom := 1 / 4
  top := 3 / 4
  bottom_pos := by norm_num
  ordered := by norm_num
  top_lt_one := by norm_num
  no_inputs := rfl
  no_outputs := rfl
  wire_clear := by
    intro w y hy _ equal
    change x w y = vertexX 0 at equal
    fin_cases w <;> norm_num [x, vertexX, Set.mem_Icc] at hy equal <;> linarith [hy.1, hy.2]
  vertex_clear := by intro v different _; fin_cases v <;> norm_num [drawing, vertexX] at *

private noncomputable def crossing : slide.Crossing 1 where
  lowerCut := 1 / 8
  earlyCut := 3 / 8
  lateCut := 5 / 8
  upperCut := 7 / 8
  horizontal := by norm_num [drawing, vertexX]
  lower_inside := by norm_num
  lower_bottom := by norm_num [slide]
  bottom_early := by norm_num [slide]
  early_other := by norm_num [drawing, height]
  other_late := by norm_num [drawing, height]
  late_top := by norm_num [slide]
  top_upper := by norm_num [slide]
  upper_inside := by norm_num
  «only» := by intro v _; fin_cases v <;> simp

private theorem firstCut : slide.initial.OrderedCut crossing.lowerCut [0, 1] := by
  constructor
  · intro w
    fin_cases w <;> norm_num [crossing, slide, drawing, Diagram.crosses, Diagram.lower, Diagram.upper,
      Diagram.NullarySlide.initial, Diagram.NullarySlide.atHeight, Diagram.NullarySlide.assemble,
      Diagram.NullarySlide.heights, height, endpointHeight, Set.mem_Ioo]
  · change [0, 1].Pairwise (fun w z : Fin 2 => x w (1 / 8) < x z (1 / 8))
    norm_num [x]

private theorem lastCut : slide.terminal.OrderedCut crossing.upperCut [] := by
  constructor
  · intro w
    fin_cases w <;> norm_num [crossing, slide, drawing, Diagram.crosses, Diagram.lower, Diagram.upper,
      Diagram.NullarySlide.terminal, Diagram.NullarySlide.atHeight, Diagram.NullarySlide.assemble,
      Diagram.NullarySlide.heights, height, endpointHeight, Set.mem_Ioo]
  · exact .nil

/-- Both incoming ports keep their coordinate order across the local comparison. -/
example : ∃ r : crossing.Readback,
    r.tie.inputWires = [0, 1] ∧ r.tie.outputWires = [] ∧
    Sheet.Move signature r.tiedSheet r.earlySheet ∧ Sheet.Move signature r.tiedSheet r.lateSheet := by
  obtain ⟨r⟩ := crossing.exists_readback
  refine ⟨r, ?_, ?_, r.splits⟩
  · rw [← r.early_input]
    exact ProgressiveGraph.Diagram.ordered_cut_unique r.early.firstEvent.before firstCut
  · rw [← r.late_output]
    exact ProgressiveGraph.Diagram.ordered_cut_unique r.late.secondEvent.after lastCut

end Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing.Regression
