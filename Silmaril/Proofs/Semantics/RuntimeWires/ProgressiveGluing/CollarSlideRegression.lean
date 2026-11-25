module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarSlide
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing.CollarSlideRegression

open ProgressiveGraph

private abbrev signature : Signature Unit where
  Edge := Unit
  source _ := []
  target _ := []

private noncomputable def column (upper : Bool) : ℝ := if upper then 3 / 4 else 1 / 4

private noncomputable def straight (upper : Bool) : Wire 0 1 where
  x _ := column upper
  increasing := by norm_num
  continuous := continuousOn_const
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    ring

/-- One moving scalar and one cap-to-cap strand. The opposite cap
coordinates differ, so the glued wire traverses a slanted collar. -/
private noncomputable def operand (upper : Bool) : ProgressiveGraph.Diagram signature 1 1 .point where
  vertexX _ := 1 / 2
  vertexHeight _ := 1 / 2
  vertex_inside _ := by norm_num [Set.mem_Ioo]
  vertex_separation := fun {_ _} _ => Subsingleton.elim _ _
  generator _ := ()
  label _ := ()
  start _ := none
  finish _ := none
  wire _ := straight upper
  wire_inside _ _ _ := by cases upper <;> norm_num [column, straight, Set.mem_Ioo]
  start_attached := by simp
  finish_attached := by simp
  separated := fun ne => (ne (Subsingleton.elim _ _)).elim
  avoids_vertex := by
    intro _ _ _
    cases upper <;> norm_num [column, straight]
  input_boundary_separated := fun ne => (ne (Subsingleton.elim _ _)).elim
  output_boundary_separated := fun ne => (ne (Subsingleton.elim _ _)).elim
  input _ := Fin.elim0
  output _ := Fin.elim0
  input_exact := by simp [signature]
  output_exact := by simp [signature]
  input_types := by simp [List.ofFn_zero]
  output_types := by simp [List.ofFn_zero]
  input_order _ {i} := Fin.elim0 i
  output_order _ {i} := Fin.elim0 i

private noncomputable def move (upper : Bool) : (operand upper).NullarySlide 0 where
  bottom := 1 / 4
  top := 3 / 4
  bottom_pos := by norm_num
  ordered := by norm_num
  top_lt_one := by norm_num
  no_inputs := rfl
  no_outputs := rfl
  wire_clear := by
    intro _ _ _ _
    change column upper ≠ (1 / 2 : ℝ)
    cases upper <;> norm_num [column]
  vertex_clear v different _ := (different (Subsingleton.elim v 0)).elim

private noncomputable def matched : (operand false).OrderedVerticalMatch (operand true) where
  contact :=
    { toFun := fun _ => ⟨0, rfl⟩
      invFun := fun _ => ⟨0, rfl⟩
      left_inv := fun _ => Subtype.ext (Subsingleton.elim ..)
      right_inv := fun _ => Subtype.ext (Subsingleton.elim ..) }
  label _ := rfl
  order _ _ := by
    change column false < column false ↔ column true < column true
    simp

private abbrev lowerContact : Diagram.PartialVerticalMatch.Contact (operand false) := ⟨0, rfl⟩
private noncomputable def traceId := matched.upperJoin.upperId (matched.contact lowerContact).val

private theorem collar_midpoint : matched.upperJoin.glue.x traceId (3 / 8) = 1 / 2 := by
  have h := matched.glue_x_in_collar lowerContact (y := 3 / 8) (by norm_num [Set.mem_Icc])
  rw [matched.glue_eq_upperJoin] at h
  exact h.trans (by
    change interpolate (1 / 4) (3 / 4) (4 * (3 / 8 : ℝ) - 1) = 1 / 2
    norm_num [interpolate])

private def zeroTime : Diagram.NullarySlide.Time := ⟨0, le_rfl, zero_le_one⟩
private def oneTime : Diagram.NullarySlide.Time := ⟨1, zero_le_one, le_rfl⟩

example : (matched.liftLowerSlide (move false)).heightAt zeroTime = 1 / 16 := by
  rw [matched.lowerSlide_heightAt]
  norm_num [halfHeight, Diagram.NullarySlide.heightAt, move, zeroTime]

example : (matched.liftUpperSlide (move true)).heightAt oneTime = 7 / 8 := by
  rw [matched.upperSlide_heightAt]
  norm_num [halfHeight, Diagram.NullarySlide.heightAt, move, oneTime]

/-- Both paths keep the same common wire at the same slanted collar point
throughout the slide, using its renamed ID in the composite. -/
example (t : Diagram.NullarySlide.Time) :
    ((matched.liftLowerSlide (move false)).frame t).x traceId (3 / 8) = 1 / 2 ∧
    ((matched.liftUpperSlide (move true)).frame t).x traceId (3 / 8) = 1 / 2 := by
  exact ⟨(congrArg Prod.fst ((matched.liftLowerSlide (move false)).wire_point
    ((matched.liftLowerSlide (move false)).height_mem t) traceId (3 / 8))).trans collar_midpoint,
    (congrArg Prod.fst ((matched.liftUpperSlide (move true)).wire_point
      ((matched.liftUpperSlide (move true)).height_mem t) traceId (3 / 8))).trans collar_midpoint⟩

example (t : Diagram.NullarySlide.Time) :
    ((matched.liftUpperSlide (move true)).frame t) =
      (matched.upperJoin.matchAtUpper (move true) ((move true).height_mem t)).glue :=
  matched.upperSlide_frame (move true) t

example (t : Diagram.NullarySlide.Time) :
    ((matched.firstLowerSlide (move false)).frame t) =
      (matched.lowerJoin.matchAtLower (move false) ((move false).height_mem t)).glue :=
  matched.firstLowerSlide_frame (move false) t

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing.CollarSlideRegression
