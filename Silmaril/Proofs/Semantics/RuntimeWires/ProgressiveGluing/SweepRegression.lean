module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Sweep
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing.SweepRegression

open ProgressiveGraph

private abbrev signature : Signature Unit where
  Edge := Option Bool
  source e := if e = some true then [()] else []
  target e := if e = some false then [()] else []

private noncomputable def height (j : Fin 3) : ℝ := if j = 1 then 1 / 4 else 1 / 2
private noncomputable def position (rising : Bool) (j : Fin 3) : ℝ :=
  if j = 0 then (if rising then 1 / 4 else 1 / 2) else 1 / 8
private def box (rising : Bool) (j : Fin 3) : Option Bool :=
  if j = 0 then some (!rising) else none

private def start (rising : Bool) : Option (Fin 3) := if rising then some 0 else none
private def finish (rising : Bool) : Option (Fin 3) := if rising then none else some 0

private noncomputable def path (rising : Bool) :
    Wire (endpointHeight height 0 (start rising)) (endpointHeight height 1 (finish rising)) where
  x y := if rising then y / 2 else 1 / 2
  increasing := by cases rising <;> norm_num [height, start, finish, endpointHeight]
  continuous := by
    cases rising
    · exact continuousOn_const
    · exact continuous_id.continuousOn.div_const 2
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    cases rising <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

/-- Two levels, with vertex 2 tied with the source or sink at vertex 0.
Vertex 1 is an earlier scalar. The matched strand is diagonal below the join
and vertical above it. -/
private noncomputable def drawing (rising : Bool) : ProgressiveGraph.Diagram signature 3 1 .point where
  vertexX := position rising
  vertexHeight := height
  vertex_inside := by
    intro v
    fin_cases v <;> cases rising <;> norm_num [position, height, Set.mem_Ioo]
  vertex_separation := by
    intro v w h
    fin_cases v <;> fin_cases w <;> cases rising <;> norm_num [position, height] at *
  generator := box rising
  label _ := ()
  start _ := start rising
  finish _ := finish rising
  wire _ := path rising
  wire_inside := by
    intro w y h
    cases rising
    · norm_num [path, Set.mem_Ioo]
    · change (1 / 2 : ℝ) ≤ y ∧ y ≤ 1 at h
      change 0 < y / 2 ∧ y / 2 < 1
      constructor <;> linarith [h.1, h.2]
  start_attached := by
    intro w v hv
    cases rising <;> simp [start] at hv
    subst v
    norm_num [path, start, endpointHeight, height, position]
  finish_attached := by
    intro w v hv
    cases rising <;> simp [finish] at hv
    subst v
    norm_num [path, finish, endpointHeight, height, position]
  separated := fun ne => (ne (Subsingleton.elim _ _)).elim
  avoids_vertex := by
    intro w v h
    fin_cases v <;> cases rising <;>
      norm_num [path, start, finish, height, position, endpointHeight, Set.mem_Ioo] at *
  input_boundary_separated := fun ne => (ne (Subsingleton.elim _ _)).elim
  output_boundary_separated := fun ne => (ne (Subsingleton.elim _ _)).elim
  input _ _ := 0
  output _ _ := 0
  input_exact := by
    intro v w
    have hw : w = 0 := Subsingleton.elim _ _
    subst w
    fin_cases v <;> cases rising <;> simp [signature, box, finish]
  output_exact := by
    intro v w
    have hw : w = 0 := Subsingleton.elim _ _
    subst w
    fin_cases v <;> cases rising <;> simp [signature, box, start]
  input_types := by
    intro v
    fin_cases v <;> cases rising <;> simp [box, List.ofFn_succ]
  output_types := by
    intro v
    fin_cases v <;> cases rising <;> simp [box, List.ofFn_succ]
  input_order := by
    intro v i j h
    have eq : i = j := Fin.ext (by
      have hj := j.isLt
      change j.val < (signature.source (box rising v)).length at hj
      have small : (signature.source (box rising v)).length ≤ 1 := by
        change (if box rising v = some true then [()] else []).length ≤ 1
        split <;> simp
      omega)
    exact (h.ne eq).elim
  output_order := by
    intro v i j h
    have eq : i = j := Fin.ext (by
      have hj := j.isLt
      change j.val < (signature.target (box rising v)).length at hj
      have small : (signature.target (box rising v)).length ≤ 1 := by
        change (if box rising v = some false then [()] else []).length ≤ 1
        split <;> simp
      omega)
    exact (h.ne eq).elim

private theorem matched : (drawing true).VerticalMatch (drawing false) where
  lower_cap _ := rfl
  upper_cap _ := rfl
  label _ := rfl
  coordinate _ := rfl

private theorem operand_levels (rising : Bool) :
    (drawing rising).levels = [1 / 4, 1 / 2] := by
  have image : Finset.univ.image (drawing rising).vertexHeight = ({1 / 4, 1 / 2} : Finset ℝ) := by
    ext h
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨v, rfl⟩
      fin_cases v <;> norm_num [drawing, height]
    · rintro (rfl | rfl)
      · exact ⟨1, by norm_num [drawing, height]⟩
      · exact ⟨0, by norm_num [drawing, height]⟩
  rw [Diagram.levels, image, Finset.sort_insert (· ≤ ·) (by intro b hb; simp at hb; rw [hb]; norm_num)
    (by norm_num), Finset.sort_singleton]

example : matched.glue.levels = [1 / 8, 1 / 4, 5 / 8, 3 / 4] := by
  rw [matched.levels_glue, operand_levels, operand_levels]
  norm_num [halfHeight]

/-- Both operand sweeps put the scalar to the left of the tied source or sink. -/
example (rising : Bool) :
    ((drawing rising).layerSweep.layer ((drawing rising).levelIndex 0)).vertices = [2, 0] := by
  let d := drawing rising
  let row := d.layerSweep.layer (d.levelIndex 0)
  have ordered : ([2, 0] : List (Fin 3)).Pairwise (fun v w => d.vertexX v < d.vertexX w) := by
    cases rising <;> norm_num [d, drawing, position, List.pairwise_cons]
  have nd := row.vertices_order.imp (fun h => ne_of_apply_ne d.vertexX (ne_of_lt h))
  have perm := (List.perm_ext_iff_of_nodup nd (by decide : ([2, 0] : List (Fin 3)).Nodup)).mpr
    (fun v => by
      rw [row.vertices_exact, d.levelHeight_index]
      fin_cases v <;> norm_num [d, drawing, height])
  exact perm.eq_of_pairwise (fun _ _ _ _ h k => (lt_asymm h k).elim) row.vertices_order ordered

private noncomputable def lowerRead := (drawing true).layerSweep
private noncomputable def upperRead := (drawing false).layerSweep

private noncomputable def atJoin := matched.glue.layerSweepAt
  (matched.spliceSweepCuts lowerRead.cuts upperRead.cuts)

example : atJoin.cuts.height matched.spliceSweepCut = 1 / 2 := by
  unfold atJoin
  rw [Diagram.layerSweepAt_cuts, matched.spliceSweepCuts_join]

example : atJoin.wires matched.spliceSweepCut = [0] := by
  apply Diagram.ordered_cut_unique (matched.sweep_ordered_at_join atJoin)
  exact ⟨fun w => ⟨fun _ => matched.crosses_join w,
    fun _ => List.mem_singleton.mpr (Subsingleton.elim w 0)⟩, List.pairwise_singleton _ _⟩

/-- The midpoint sweep of the composite may choose different cuts.
Its whole typed sheet still agrees with the independently read operands. -/
example :
    let glued := matched.glue.layerSweep
    glued.sheet.reindex (matched.sweep_first_word lowerRead glued) (matched.sweep_last_word upperRead glued) =
      lowerRead.sheet.thenDo (upperRead.sheet.reindex (matched.sweep_join_word lowerRead upperRead) rfl) :=
  matched.sweep_concat lowerRead upperRead matched.glue.layerSweep

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing.SweepRegression
