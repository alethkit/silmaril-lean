module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSimultaneous.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous.LayerRegression

open Silmaril.RuntimeWires.ProgressiveGraph

private abbrev signature : Signature Bool where
  Edge := Fin 3
  source _ := []
  target j := if j = 2 then [true] else []

private noncomputable def vertexX (j : Fin 3) : ℝ :=
  if j = 0 then 3 / 8 else if j = 1 then 1 / 4 else 3 / 4

private noncomputable def height (_ : Fin 3) : ℝ := 1 / 2

private def start (w : Fin 2) : Option (Fin 3) := if w = 0 then none else some 2

private noncomputable def x (w : Fin 2) (y : ℝ) : ℝ :=
  if w = 0 then (3 + y) / 8 else (5 + 2 * y) / 8

private noncomputable def strand (w : Fin 2) :
    Wire (endpointHeight height 0 (start w)) 1 where
  x := x w
  increasing := by fin_cases w <;> norm_num [start, height, endpointHeight]
  continuous := by
    unfold x
    split <;> exact (by fun_prop : Continuous _).continuousOn
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold x
    split <;> ring

/-- Two adjacent scalars lie to the left of a passing wire. The third
vertex creates a wire and lies to its right. -/
private noncomputable def drawing : Diagram signature 3 2 .point where
  vertexX := vertexX
  vertexHeight := height
  vertex_inside := by intro j; fin_cases j <;> norm_num [vertexX, height, Set.mem_Ioo]
  vertex_separation := by
    intro i j he
    have hx := congrArg Prod.fst he
    fin_cases i <;> fin_cases j <;> norm_num [vertexX] at *
  generator := id
  label := fun i => decide (i = 1)
  start := start
  finish _ := none
  wire := strand
  wire_inside := by
    intro w y hy
    fin_cases w <;> norm_num [strand, x, start, height, endpointHeight,
      Set.mem_Icc, Set.mem_Ioo] at * <;>
      constructor <;> linarith [hy.1, hy.2]
  start_attached := by
    intro w j he
    fin_cases w <;> fin_cases j <;> norm_num [start, height, vertexX, strand, x] at *
  finish_attached := by simp
  separated := by
    intro w z hw y ha hb
    fin_cases w <;> fin_cases z
    all_goals norm_num [strand, x, start, height, endpointHeight, Set.mem_Icc, Set.mem_Ioo] at *
    all_goals
      intro he
      linarith [ha.1, ha.2, hb.1, hb.2]
  avoids_vertex := by
    intro w j hw
    fin_cases w <;> fin_cases j <;>
      norm_num [strand, x, vertexX, height, start, endpointHeight, Set.mem_Ioo] at *
  input_boundary_separated := by
    intro w z hw hs ht
    fin_cases w <;> fin_cases z <;> norm_num [start, strand, x] at *
  output_boundary_separated := by
    intro w z hw hs ht
    fin_cases w <;> fin_cases z <;> norm_num [strand, x] at *
  input _ i := Fin.elim0 i
  output _ _ := 1
  input_exact := by
    intro j w
    change (none : Option (Fin 3)) = some j ↔ ∃ i : Fin 0, Fin.elim0 i = w
    simp
  output_exact := by
    intro j w
    fin_cases j <;> fin_cases w <;> simp [signature, start]
  input_types := by intro j; rfl
  output_types := by intro j; fin_cases j <;> simp [List.ofFn_succ]
  input_order := by intro j i; exact Fin.elim0 i
  output_order := by
    intro j i k hij
    have small : (signature.target (id j)).length ≤ 1 := by fin_cases j <;> decide
    omega

private theorem layer : drawing.IsolatesLayer (1 / 2) (1 / 4) (3 / 4) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun _ _ => rfl⟩

private noncomputable def slice := Classical.choice (Diagram.layer_slice layer)

private abbrev expected : List (Diagram.LayerSlot 3 2) :=
  [.inr 1, .inr 0, .inl 0, .inr 2]

private theorem expected_exact (c : Diagram.LayerSlot 3 2) :
    c ∈ expected ↔ drawing.atLayer (1 / 2) c := by
  cases c with
  | inl w =>
    fin_cases w <;>
      norm_num [expected, drawing, Diagram.atLayer, Diagram.crosses, Diagram.lower,
        Diagram.upper, endpointHeight, height, start, Set.mem_Ioo]
  | inr j => fin_cases j <;> norm_num [expected, Diagram.atLayer, drawing, height]

private theorem expected_order :
    expected.Pairwise (fun a b => drawing.slotX (1 / 2) a < drawing.slotX (1 / 2) b) := by
  have point (w : Fin 2) (y : ℝ) : (drawing.wire w).x y = x w y := rfl
  simp only [expected, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  norm_num [Diagram.slotX, Diagram.x, point, drawing, vertexX, x]

/-- The two nullary cells are consecutive in the actual geometrically
sorted slot list, despite having no incident wire IDs. -/
private theorem slots : slice.slots = expected := by
  have nd : slice.slots.Nodup := slice.ordered.imp
    (fun h => ne_of_apply_ne (drawing.slotX (1 / 2)) (ne_of_lt h))
  have perm := (List.perm_ext_iff_of_nodup nd (by simp [expected])).mpr
    (fun c => (slice.exact_slots c).trans (expected_exact c).symm)
  exact perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim)
    slice.ordered expected_order

example : slice.vertices = [1, 0, 2] := by
  rw [Diagram.LayerSlice.vertices, slots]
  rfl

example : drawing.OrderedCut (1 / 4) [0] ∧ drawing.OrderedCut (3 / 4) [0, 1] := by
  have h := slice.before
  have k := slice.after
  rw [slots] at h k
  exact ⟨h, k⟩

/-- The ordered typed row reads all three generators, including the two
that produce no contribution to either ordered cut word. -/
example : slice.row.boxCount = 3 := by
  rw [Diagram.LayerSlice.row, slots]
  rfl

noncomputable example : Silmaril.RuntimeWires.Sliced.Row signature [false] [false, true] := by
  have h := slice.cutRow
  rw [slots] at h
  exact h

end Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous.LayerRegression
