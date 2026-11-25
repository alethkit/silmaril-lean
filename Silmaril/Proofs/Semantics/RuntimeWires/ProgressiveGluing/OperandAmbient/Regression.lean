module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Thms
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.OperandAmbient.Regression

open ProgressiveGraph SlabIsotopy

private abbrev signature : Signature Bool where
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

private noncomputable def tent (y : ℝ) : ℝ := max 0 (min y (1 - y))

private theorem tent_low {y : ℝ} (hy : 0 ≤ y) (h : y ≤ 1 / 2) : tent y = y := by
  unfold tent
  rw [min_eq_left (by linarith), max_eq_right hy]

private theorem tent_high {y : ℝ} (hy : y ≤ 1) (h : 1 / 2 ≤ y) : tent y = 1 - y := by
  unfold tent
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

private theorem tent_outside {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) : tent y = 0 := by
  unfold tent
  apply max_eq_left
  rcases h with low | high
  · exact (min_le_left _ _).trans low
  · exact (min_le_right _ _).trans (by linarith)

private theorem tent_range (y : ℝ) : tent y ∈ Set.Icc 0 (1 / 2) := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  rcases le_total y (1 / 2 : ℝ) with low | high
  · exact (min_le_left _ _).trans low
  · exact (min_le_right _ _).trans (by linarith)

private theorem tent_cont : Continuous tent := by
  unfold tent
  fun_prop

private noncomputable def displacement (t : Time) (y : ℝ) : ℝ := t.val * tent y / 3

private theorem displacement_cont :
    Continuous (fun z : Time × (ℝ × ℝ) => displacement z.1 z.2.2) :=
  ((continuous_subtype_val.comp continuous_fst).mul
    (tent_cont.comp (continuous_snd.comp continuous_snd))).div_const 3

private noncomputable def shearFrame (t : Time) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (z.1 + displacement t z.2, z.2)
  invFun z := (z.1 - displacement t z.2, z.2)
  left_inv _ := Prod.ext (add_sub_cancel_right ..) rfl
  right_inv _ := Prod.ext (sub_add_cancel ..) rfl
  continuous_toFun := (continuous_fst.add (displacement_cont.comp
    (continuous_const.prodMk continuous_id))).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub (displacement_cont.comp
    (continuous_const.prodMk continuous_id))).prodMk continuous_snd

private noncomputable def shear : SlabIsotopy where
  frame := shearFrame
  zero z := by
    change (z.1 + displacement ⟨0, le_rfl, zero_le_one⟩ z.2, z.2) = z
    exact Prod.ext (by norm_num [displacement]) rfl
  continuous_frame := ((continuous_fst.comp continuous_snd).add displacement_cont).prodMk
    (continuous_snd.comp continuous_snd)
  continuous_inverse := ((continuous_fst.comp continuous_snd).sub displacement_cont).prodMk
    (continuous_snd.comp continuous_snd)
  height _ _ := rfl
  outside t z h := by
    change (z.1 + displacement t z.2, z.2) = z
    exact Prod.ext (by simp [displacement, tent_outside h]) rfl

private noncomputable def bend (t : Time) : Wire 0 1 where
  x y := 1 / 3 + displacement t y
  increasing := by norm_num
  continuous := (continuous_const.add
    (displacement_cont.comp (continuous_const.prodMk
      ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).prodMk continuous_id)))).continuousOn
  polygonal := by
    refine ⟨{1 / 2}, ?_⟩
    intro a ha b hb ab clear s hs
    let y := (1 - s) * a + s * b
    have ay : a ≤ y := by dsimp [y]; nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr ab.le)]
    have yb : y ≤ b := by
      dsimp [y]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ab.le)]
    change 1 / 3 + displacement t y =
      (1 - s) * (1 / 3 + displacement t a) + s * (1 / 3 + displacement t b)
    unfold displacement
    by_cases high : b ≤ 1 / 2
    · rw [tent_low (ha.1.trans ay) (yb.trans high), tent_low ha.1 (ab.le.trans high), tent_low hb.1 high]
      dsimp [y]
      ring
    · have lo : (1 / 2 : ℝ) ≤ a := by
        by_contra! h
        exact clear (1 / 2) (Finset.mem_singleton_self _) ⟨h, lt_of_not_ge high⟩
      rw [tent_high (yb.trans hb.2) (lo.trans ay), tent_high ha.2 lo, tent_high hb.2 (lo.trans ab.le)]
      dsimp [y]
      ring

private noncomputable def drawing (t : Time) : ProgressiveGraph.Diagram signature 0 1 .point where
  vertexX := Fin.elim0
  vertexHeight := Fin.elim0
  vertex_inside := fun j => j.elim0
  vertex_separation := fun {j} => j.elim0
  generator := Fin.elim0
  label _ := true
  start _ := none
  finish _ := none
  wire _ := bend t
  wire_inside _ y _ := by
    have ht := tent_range y
    have nonneg : 0 ≤ displacement t y := div_nonneg (mul_nonneg t.property.1 ht.1) (by norm_num)
    have upper : displacement t y ≤ 1 / 6 := by
      unfold displacement
      linarith [mul_le_of_le_one_left ht.1 t.property.2, ht.2]
    change 1 / 3 + displacement t y ∈ Set.Ioo (0 : ℝ) 1
    exact ⟨by linarith, by linarith⟩
  start_attached _ := fun j => j.elim0
  finish_attached _ := fun j => j.elim0
  separated ne := (ne (Subsingleton.elim _ _)).elim
  avoids_vertex _ := fun j => j.elim0
  input_boundary_separated ne := (ne (Subsingleton.elim _ _)).elim
  output_boundary_separated ne := (ne (Subsingleton.elim _ _)).elim
  input j := j.elim0
  output j := j.elim0
  input_exact j := j.elim0
  output_exact j := j.elim0
  input_types j := j.elim0
  output_types j := j.elim0
  input_order j := j.elim0
  output_order j := j.elim0

private noncomputable def initial := drawing ⟨0, le_rfl, zero_le_one⟩

private theorem initial_x (w : Fin 1) (y : ℝ) : initial.x w y = 1 / 3 := by
  change 1 / 3 + displacement ⟨0, le_rfl, zero_le_one⟩ y = _
  norm_num [displacement]

private noncomputable def motion : initial.AmbientMotion where
  isotopy := shear
  wireCount _ := 1
  drawing := drawing
  correspondence t :=
    { rename := Equiv.refl _
      heights := rfl
      generators := rfl
      label _ := rfl
      start _ := rfl
      finish _ := rfl
      inputs j := j.elim0
      outputs j := j.elim0
      wire w y _ := by
        change (initial.x w y + displacement t y, y) = (1 / 3 + displacement t y, y)
        rw [initial_x]
      vertex j := j.elim0 }

private def matchCaps : initial.OrderedVerticalMatch initial where
  contact := Equiv.refl _
  label _ := rfl
  order a b := by rw [initial_x, initial_x, initial_x, initial_x]

private noncomputable def full := matchCaps.glueOperands motion motion

private noncomputable def halfway : Time := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem upper_mid :
    full.isotopy.frame halfway (1 / 3, 3 / 4) = (5 / 12, 3 / 4) := by
  change (matchCaps.glueOperands motion motion).isotopy.frame halfway (1 / 3, 3 / 4) = _
  rw [matchCaps.glueOperands_upper motion motion _ _ (by norm_num)]
  change (1 / 3 + displacement halfway (slabHeight 1 (3 / 4)),
    halfHeight 1 (slabHeight 1 (3 / 4))) = _
  norm_num [displacement, tent, halfway, slabHeight, halfHeight]

/-- Both operand interiors move. The normalized midpoint is carried to
height 1/8 in the lower operand and height 3/4 in the upper operand. -/
example :
    full.isotopy.frame halfway (1 / 3, 1 / 8) = (5 / 12, 1 / 8) ∧
    full.isotopy.frame halfway (1 / 3, 3 / 4) = (5 / 12, 3 / 4) ∧
    full.isotopy.frame halfway (1 / 3, 3 / 8) = (1 / 3, 3 / 8) := by
  refine ⟨?_, upper_mid, matchCaps.glueOperands_collar motion motion _ _ (by norm_num [Set.mem_Icc])⟩
  change (matchCaps.glueOperands motion motion).isotopy.frame halfway (1 / 3, 1 / 8) = _
  rw [matchCaps.glueOperands_lower motion motion _ _ (by norm_num)]
  change (1 / 3 + displacement halfway (slabHeight 0 (slabHeight 0 (1 / 8))),
    halfHeight 0 (halfHeight 0 (slabHeight 0 (slabHeight 0 (1 / 8))))) = _
  norm_num [displacement, tent, halfway, slabHeight, halfHeight]

private noncomputable def sharedWire := matchCaps.upperJoin.upperId 0

private theorem wire_covers (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    matchCaps.glue.covers sharedWire y := by
  have lo : matchCaps.glue.start sharedWire = none := by
    cases h : matchCaps.glue.start sharedWire with
    | none => rfl
    | some v => exact v.elim0
  have hi : matchCaps.glue.finish sharedWire = none := by
    cases h : matchCaps.glue.finish sharedWire with
    | none => rfl
    | some v => exact v.elim0
  simpa only [ProgressiveGraph.Diagram.covers, ProgressiveGraph.Diagram.lower,
    ProgressiveGraph.Diagram.upper, lo, hi, endpointHeight, Option.elim_none] using hy

/-- The upper operand's moving midpoint is the point at the same height
on the actual renamed, re-glued wire. -/
example :
    (full.drawing halfway).x ((full.correspondence halfway).rename sharedWire) (3 / 4) = 5 / 12 := by
  have source : matchCaps.glue.x sharedWire (3 / 4) = 1 / 3 := by
    rw [matchCaps.glue_eq_upperJoin]
    exact (matchCaps.upperJoin.glue_x_upper 0 (by norm_num)).trans (initial_x _ _)
  have h := (full.correspondence halfway).wire sharedWire (3 / 4)
    (wire_covers _ (by norm_num [Set.mem_Icc]))
  rw [source, upper_mid] at h
  exact (congrArg Prod.fst h).symm

/-- After the two splices the whole shared trace moves under one homeomorphism. -/
example :
    full.isotopy.frame halfway '' (matchCaps.glue.wire sharedWire).trace =
      ((full.drawing halfway).wire ((full.correspondence halfway).rename sharedWire)).trace :=
  (full.correspondence halfway).trace sharedWire

end Silmaril.RuntimeWires.Proofs.OperandAmbient.Regression
