module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarSlide
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepReadback
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

private noncomputable def cap (upper : Bool) : FixedCap signature where
  profile :=
    { size := 1
      label _ := ()
      x _ := column upper
      ordered := fun {i j} lt => (lt.ne (Subsingleton.elim i j)).elim }
  inside _ := by cases upper <;> norm_num [column, Set.mem_Ioo]

private noncomputable def fixed (upper : Bool) :
    FixedDrawing signature (cap upper).profile (cap upper).profile where
  vertices := 1
  wires := 1
  drawing := operand upper
  input := (Equiv.subtypeUnivEquiv fun _ => rfl).symm
  output := (Equiv.subtypeUnivEquiv fun _ => rfl).symm
  input_label _ := rfl
  output_label _ := rfl
  input_x _ := rfl
  output_x _ := rfl

private theorem one_row (upper : Bool) : (fixed upper).readSheet.cells.length = 1 := by
  simp only [FixedDrawing.readSheet, FixedDrawing.readSheetAt, Sliced.Sheet.cells_reindex,
    Diagram.LayerSweep.sheet, Proofs.ProgressiveGluing.cells_joinRows, List.length_ofFn]
  rw [Diagram.levelCount, Diagram.levels, Finset.length_sort]
  change ((Finset.univ : Finset (Fin 1)).image (fun _ => (1 / 2 : ℝ))).card = 1
  rw [Finset.image_const Finset.univ_nonempty, Finset.card_singleton]

private theorem same_types : (cap false).types = (cap true).types := rfl

/-- An interpolation between the two distinct cap coordinates contributes
no row between the two scalar events in the collared composite. -/
example :
    (((fixed false).thenDo (FixedCap.interpolationDrawing same_types)).thenDo
      (fixed true)).readSheet.cells.length = 2 := by
  have collar : (FixedCap.interpolationDrawing same_types).readSheet.cells = [] := by
    have empty := congrArg Sliced.Sheet.cells
      ((FixedCap.interpolationDrawing same_types).readSheet_vertexFree rfl same_types)
    exact empty.trans ((Sliced.Sheet.cells_reindex rfl same_types _).trans Sliced.Sheet.cells_empty)
  rw [FixedDrawing.readSheet_thenDo, FixedDrawing.readSheet_thenDo,
    Proofs.ProgressiveGluing.cells_thenDo, Proofs.ProgressiveGluing.cells_thenDo, collar,
    List.append_nil, List.length_append, one_row false, one_row true]

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing.CollarSlideRegression
