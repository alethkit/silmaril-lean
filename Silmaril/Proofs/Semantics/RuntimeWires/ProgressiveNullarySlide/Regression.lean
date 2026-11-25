module

public import Silmaril.Semantics.RuntimeWires.ProgressiveNullarySlide.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveNullarySlide.Regression

open ProgressiveGraph Sliced

private abbrev signature : Signature (Fin 3) where
  Edge := Fin 2
  source v := if v = 0 then [] else [1]
  target v := if v = 0 then [] else [2]

private noncomputable def vertexX (v : Fin 2) : ℝ := if v = 0 then 1 / 3 else 11 / 16
private noncomputable def height (_ : Fin 2) : ℝ := 1 / 2
private def start (w : Fin 3) : Option (Fin 2) := if w = 2 then some 1 else none
private def finish (w : Fin 3) : Option (Fin 2) := if w = 1 then some 1 else none

private noncomputable def x (w : Fin 3) (y : ℝ) : ℝ :=
  if w = 0 then (2 + y) / 16 else if w = 1 then (5 + y) / 8 else (6 - y) / 8

private noncomputable def strand (w : Fin 3) :
    Wire (endpointHeight height 0 (start w)) (endpointHeight height 1 (finish w)) where
  x := x w
  increasing := by fin_cases w <;> norm_num [start, finish, height, endpointHeight]
  continuous := by
    unfold x
    split
    · exact (by fun_prop : Continuous _).continuousOn
    · split <;> exact (by fun_prop : Continuous _).continuousOn
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold x
    split
    · ring
    · split <;> ring

/-- One slanted cap-to-cap strand passes to the left of the scalar's path.
On its right, a unary box changes the label on a bent strand. -/
private noncomputable def drawing : Diagram signature 2 3 .point where
  vertexX := vertexX
  vertexHeight := height
  vertex_inside := by intro v; fin_cases v <;> norm_num [vertexX, height, Set.mem_Ioo]
  vertex_separation := by
    intro i j he
    have hx := congrArg Prod.fst he
    fin_cases i <;> fin_cases j <;> norm_num [vertexX] at *
  generator := id
  label := id
  start := start
  finish := finish
  wire := strand
  wire_inside := by
    intro w y hy
    fin_cases w <;> norm_num [strand, x, start, finish, height, endpointHeight,
      Set.mem_Icc, Set.mem_Ioo] at * <;> constructor <;> linarith [hy.1, hy.2]
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
  input := fun _ _ => 1
  output := fun _ _ => 2
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

private theorem initial_x (w : Fin 3) (y : ℝ) : (slide.initial.wire w).x y = x w y := rfl

private theorem terminal_x (w : Fin 3) (y : ℝ) : (slide.terminal.wire w).x y = x w y := rfl

private noncomputable def halfway : Diagram.NullarySlide.Time := ⟨1 / 2, by norm_num [Set.mem_Icc]⟩

private theorem unique_tie : ∃! t : Diagram.NullarySlide.Time,
    (slide.frame t).IsolatesPair 0 1 (1 / 8) (7 / 8) := by
  apply slide.isolated_crossing
  · norm_num [drawing, vertexX]
  · norm_num [drawing, height, slide, Set.mem_Ioo]
  · norm_num
  · norm_num [slide]
  · norm_num [slide]
  · norm_num
  · intro v _; fin_cases v <;> simp

private noncomputable def tied : Diagram signature 2 3 .point := slide.frame halfway

private theorem tied_height (v : Fin 2) : tied.vertexHeight v = 1 / 2 := by
  fin_cases v <;> norm_num [tied, Diagram.NullarySlide.frame, Diagram.NullarySlide.atHeight,
    Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, Diagram.NullarySlide.heightAt,
    slide, halfway, drawing, height]

private theorem tied_pair : tied.IsolatesPair 0 1 (1 / 8) (7 / 8) := by
  refine ⟨(tied_height 1).trans (tied_height 0).symm, ?_, by norm_num, ?_, ?_, by norm_num, ?_⟩
  · change vertexX 0 < vertexX 1
    norm_num [vertexX]
  · rw [tied_height]
    norm_num
  · rw [tied_height]
    norm_num
  · intro v _; fin_cases v <;> simp

private theorem tied_x (w : Fin 3) (y : ℝ) : tied.x w y = x w y := rfl

private theorem beforeCut {y : ℝ} (lo : 0 < y) (hi : y < 1 / 2) : drawing.OrderedCut y [0, 1] := by
  constructor
  · intro w
    fin_cases w <;>
      norm_num [drawing, Diagram.crosses, Diagram.lower, Diagram.upper, endpointHeight,
        start, finish, height, Set.mem_Ioo] <;> (try constructor) <;> (try intro h) <;> linarith
  · norm_num [drawing, Diagram.x, strand, x]
    change x 0 y < x 1 y
    norm_num [x]
    linarith

private theorem afterCut {y : ℝ} (lo : 1 / 2 < y) (hi : y < 1) : drawing.OrderedCut y [0, 2] := by
  constructor
  · intro w
    fin_cases w <;>
      norm_num [drawing, Diagram.crosses, Diagram.lower, Diagram.upper, endpointHeight,
        start, finish, height, Set.mem_Ioo] <;> (try constructor) <;> (try intro h) <;> linarith
  · norm_num [drawing, Diagram.x, strand, x]
    change x 0 y < x 2 y
    norm_num [x]
    linarith

private theorem initial_height (v : Fin 2) :
    slide.initial.vertexHeight v = if v = 0 then 1 / 4 else 1 / 2 := rfl

private theorem terminal_height (v : Fin 2) :
    slide.terminal.vertexHeight v = if v = 0 then 3 / 4 else 1 / 2 := rfl

/-- The cuts actually isolate the respective vertices in the two endpoint pictures. -/
example : slide.initial.Isolates 0 (1 / 8) (3 / 8) ∧ slide.initial.Isolates 1 (3 / 8) (7 / 8) ∧
    slide.terminal.Isolates 1 (1 / 8) (5 / 8) ∧ slide.terminal.Isolates 0 (5 / 8) (7 / 8) := by
  constructor
  · refine ⟨by norm_num, by norm_num [initial_height], by norm_num [initial_height], by norm_num, ?_⟩
    intro v hv
    fin_cases v <;> norm_num [initial_height, Set.mem_Icc] at *
  refine ⟨⟨by norm_num, by norm_num [initial_height], by norm_num [initial_height], by norm_num, ?_⟩,
    ⟨by norm_num, by norm_num [terminal_height], by norm_num [terminal_height], by norm_num, ?_⟩,
    ⟨by norm_num, by norm_num [terminal_height], by norm_num [terminal_height], by norm_num, ?_⟩⟩
  all_goals
    intro v hv
    fin_cases v <;> norm_num [initial_height, terminal_height, Set.mem_Icc] at *

private noncomputable def earlyScalar : slide.initial.EventSlice 0 (1 / 8) (3 / 8) where
  left := [0]
  right := [1]
  left_exact := by
    intro w
    simp only [Diagram.x, initial_x]
    fin_cases w <;> norm_num [Diagram.NullarySlide.initial, Diagram.NullarySlide.atHeight,
      Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, slide, drawing,
      Diagram.crosses, Diagram.lower, Diagram.upper,  endpointHeight,
      start, finish, height, x, vertexX, Set.mem_Ioo]
  right_exact := by
    intro w
    simp only [Diagram.x, initial_x]
    fin_cases w <;> norm_num [Diagram.NullarySlide.initial, Diagram.NullarySlide.atHeight,
      Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, slide, drawing,
      Diagram.crosses, Diagram.lower, Diagram.upper,  endpointHeight,
      start, finish, height, x, vertexX, Set.mem_Ioo]
  before := (slide.ordered_cut_iff _).mpr (beforeCut (by norm_num) (by norm_num))
  after := (slide.ordered_cut_iff _).mpr (beforeCut (by norm_num) (by norm_num))

private noncomputable def earlyUnary : slide.initial.EventSlice 1 (3 / 8) (7 / 8) where
  left := [0]
  right := []
  left_exact := by
    intro w
    simp only [Diagram.x, initial_x]
    fin_cases w <;> norm_num [Diagram.NullarySlide.initial, Diagram.NullarySlide.atHeight,
      Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, slide, drawing,
      Diagram.crosses, Diagram.lower, Diagram.upper,  endpointHeight,
      start, finish, height, x, vertexX, Set.mem_Ioo]
  right_exact := by
    intro w
    simp only [Diagram.x, initial_x]
    fin_cases w <;> norm_num [Diagram.NullarySlide.initial, Diagram.NullarySlide.atHeight,
      Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, slide, drawing,
      Diagram.crosses, Diagram.lower, Diagram.upper,  endpointHeight,
      start, finish, height, x, vertexX, Set.mem_Ioo]
  before := (slide.ordered_cut_iff _).mpr (beforeCut (by norm_num) (by norm_num))
  after := (slide.ordered_cut_iff _).mpr (afterCut (by norm_num) (by norm_num))

private noncomputable def lateUnary : slide.terminal.EventSlice 1 (1 / 8) (5 / 8) where
  left := [0]
  right := []
  left_exact := by
    intro w
    simp only [Diagram.x, terminal_x]
    fin_cases w <;> norm_num [Diagram.NullarySlide.terminal, Diagram.NullarySlide.atHeight,
      Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, slide, drawing,
      Diagram.crosses, Diagram.lower, Diagram.upper,  endpointHeight,
      start, finish, height, x, vertexX, Set.mem_Ioo]
  right_exact := by
    intro w
    simp only [Diagram.x, terminal_x]
    fin_cases w <;> norm_num [Diagram.NullarySlide.terminal, Diagram.NullarySlide.atHeight,
      Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, slide, drawing,
      Diagram.crosses, Diagram.lower, Diagram.upper,  endpointHeight,
      start, finish, height, x, vertexX, Set.mem_Ioo]
  before := (slide.ordered_cut_iff _).mpr (beforeCut (by norm_num) (by norm_num))
  after := (slide.ordered_cut_iff _).mpr (afterCut (by norm_num) (by norm_num))

private noncomputable def lateScalar : slide.terminal.EventSlice 0 (5 / 8) (7 / 8) where
  left := [0]
  right := [2]
  left_exact := by
    intro w
    simp only [Diagram.x, terminal_x]
    fin_cases w <;> norm_num [Diagram.NullarySlide.terminal, Diagram.NullarySlide.atHeight,
      Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, slide, drawing,
      Diagram.crosses, Diagram.lower, Diagram.upper,  endpointHeight,
      start, finish, height, x, vertexX, Set.mem_Ioo]
  right_exact := by
    intro w
    simp only [Diagram.x, terminal_x]
    fin_cases w <;> norm_num [Diagram.NullarySlide.terminal, Diagram.NullarySlide.atHeight,
      Diagram.NullarySlide.assemble, Diagram.NullarySlide.heights, slide, drawing,
      Diagram.crosses, Diagram.lower, Diagram.upper,  endpointHeight,
      start, finish, height, x, vertexX, Set.mem_Ioo]
  before := (slide.ordered_cut_iff _).mpr (afterCut (by norm_num) (by norm_num))
  after := (slide.ordered_cut_iff _).mpr (afterCut (by norm_num) (by norm_num))

private noncomputable def tiedSlice : tied.LayerSlice (1 / 2) (1 / 8) (7 / 8) where
  isolation := by simpa only [tied_height] using tied_pair.toLayer
  slots := [.inl 0, .inr 0, .inr 1]
  exact_slots := by
    intro c
    cases c with
    | inl w =>
      fin_cases w <;> norm_num [Diagram.atLayer, Diagram.crosses, Diagram.lower, Diagram.upper,
        tied, Diagram.NullarySlide.frame, Diagram.NullarySlide.atHeight, Diagram.NullarySlide.assemble,
        drawing, start, finish, endpointHeight, Set.mem_Ioo, height, Diagram.NullarySlide.heights]
    | inr v => fin_cases v <;> simp [Diagram.atLayer, tied_height]
  ordered := by
    have scalarX : tied.vertexX 0 = vertexX 0 := rfl
    have unaryX : tied.vertexX 1 = vertexX 1 := rfl
    norm_num [List.pairwise_cons, Diagram.slotX, tied_x, scalarX, unaryX, x, vertexX]
  before := (slide.ordered_cut_iff (slide.height_mem halfway)).mpr (beforeCut (by norm_num) (by norm_num))
  after := (slide.ordered_cut_iff (slide.height_mem halfway)).mpr (afterCut (by norm_num) (by norm_num))

private noncomputable def tiedRow : Row signature [0, 1] [0, 2] := tiedSlice.row

/-- The two seam moves read on this deformation. The middle diagram retains
its through wire and both labeled generator occurrences. -/
example : Sheet.SeamEquivalent
    (.cons earlyScalar.row (.cons earlyUnary.row (.empty [0, 2])))
    (.cons lateUnary.row (.cons lateScalar.row (.empty [0, 2]))) := by
  have early : Row.Split signature tiedRow earlyScalar.row earlyUnary.row := by
    have split := Row.Split.wire (S := signature) 0
      (Row.Split.upper (S := signature) (0 : Fin 2) (Row.Split.lower (S := signature) (1 : Fin 2) .empty))
    exact split
  have late : Row.Split signature tiedRow lateUnary.row lateScalar.row := by
    have split := Row.Split.wire (S := signature) 0
      (Row.Split.lower (S := signature) (0 : Fin 2) (Row.Split.upper (S := signature) (1 : Fin 2) .empty))
    exact split
  exact .trans _ (.cons tiedRow (.empty _)) _
    (.symm _ _ (.rel _ _ (.split early _))) (.rel _ _ (.split late _))

end Silmaril.RuntimeWires.Proofs.ProgressiveNullarySlide.Regression
