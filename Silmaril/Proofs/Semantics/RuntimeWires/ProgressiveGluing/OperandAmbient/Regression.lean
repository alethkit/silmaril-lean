module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarCombined.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.FixedCapCategory.Thms
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

private theorem wire_covers {W : ℕ} (d : ProgressiveGraph.Diagram signature 0 W .point)
    (w : Fin W) (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) : d.covers w y := by
  have lo : d.start w = none := by
    cases d.start w with
    | none => rfl
    | some v => exact v.elim0
  have hi : d.finish w = none := by
    cases d.finish w with
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
    (wire_covers matchCaps.glue sharedWire _ (by norm_num [Set.mem_Icc]))
  rw [source, upper_mid] at h
  exact (congrArg Prod.fst h).symm

/-- After the two splices the whole shared trace moves under one homeomorphism. -/
example :
    full.isotopy.frame halfway '' (matchCaps.glue.wire sharedWire).trace =
      ((full.drawing halfway).wire ((full.correspondence halfway).rename sharedWire)).trace :=
  (full.correspondence halfway).trace sharedWire

private noncomputable def lastTime : Time := ⟨1, zero_le_one, le_rfl⟩

private theorem collar_bottom_third (w : Fin (ProgressiveGraph.Diagram.OrderedVerticalMatch.collarCount initial)) :
    matchCaps.collarSpec.bottom w = 1 / 3 := by
  rw [matchCaps.collarSpec_bottom, initial_x]

private theorem collar_top_third (w : Fin (ProgressiveGraph.Diagram.OrderedVerticalMatch.collarCount initial)) :
    matchCaps.collarSpec.top w = 1 / 3 := by
  rw [matchCaps.collarSpec_top, initial_x]

private noncomputable def bentCollar : PolygonalCollar matchCaps.collarSpec where
  wire _ := bend lastTime
  bottom w := by
    rw [collar_bottom_third]
    change 1 / 3 + displacement lastTime 0 = _
    norm_num [displacement, tent]
  top w := by
    rw [collar_top_third]
    change 1 / 3 + displacement lastTime 1 = _
    norm_num [displacement, tent]
  inside _ y hy := (drawing lastTime).wire_inside 0 y hy
  ordered a b _ _ h := by
    rw [collar_bottom_third a, collar_bottom_third b] at h
    exact ((lt_irrefl _) h).elim

private noncomputable def combined :=
  matchCaps.glueWithMotions matchCaps.straightCollar bentCollar motion motion

private noncomputable def middleId :=
  ProgressiveGraph.Diagram.OrderedVerticalMatch.collarIndex initial ⟨0, rfl⟩

private theorem middle_mid :
    combined.isotopy.frame halfway (1 / 3, 3 / 8) = (5 / 12, 3 / 8) := by
  change (matchCaps.glueWithMotions matchCaps.straightCollar bentCollar motion motion).isotopy.frame
    halfway (1 / 3, 3 / 8) = _
  rw [matchCaps.glueWithMotions_middle _ _ _ _ _ _ (by norm_num [Set.mem_Icc])]
  have h := matchCaps.straightCollar.ambientIsotopy_wire bentCollar halfway middleId (y := 3 / 8)
    (by norm_num [Set.mem_Icc])
  rw [show 4 * (3 / 8 : ℝ) - 1 = 1 / 2 by norm_num, PolygonalCollar.blend_x,
    matchCaps.straightCollar_x, collar_bottom_third, collar_top_third] at h
  change matchCaps.straightCollar.ambientIsotopy bentCollar halfway
      (interpolate (1 / 3) (1 / 3) (1 / 2), 3 / 8) =
    (interpolate (interpolate (1 / 3) (1 / 3) (1 / 2))
      (1 / 3 + displacement lastTime (1 / 2)) halfway.val, 3 / 8) at h
  norm_num [interpolate, displacement, halfway, lastTime, tent] at h
  exact h

/-- At a common time all three interior points move, using their own
placements. The inverse takes the collar midpoint back to its source. -/
example :
    combined.isotopy.frame halfway (1 / 3, 1 / 8) = (5 / 12, 1 / 8) ∧
    combined.isotopy.frame halfway (1 / 3, 3 / 8) = (5 / 12, 3 / 8) ∧
    combined.isotopy.frame halfway (1 / 3, 3 / 4) = (5 / 12, 3 / 4) ∧
    (combined.isotopy.frame halfway).symm (5 / 12, 3 / 8) = (1 / 3, 3 / 8) := by
  refine ⟨?_, middle_mid, ?_, ?_⟩
  · change (matchCaps.glueWithMotions matchCaps.straightCollar bentCollar motion motion).isotopy.frame
      halfway (1 / 3, 1 / 8) = _
    rw [matchCaps.glueWithMotions_lower _ _ _ _ _ _ (by norm_num)]
    change (1 / 3 + displacement halfway (slabHeight 0 (slabHeight 0 (1 / 8))),
      halfHeight 0 (halfHeight 0 (slabHeight 0 (slabHeight 0 (1 / 8))))) = _
    norm_num [displacement, tent, halfway, slabHeight, halfHeight]
  · change (matchCaps.glueWithMotions matchCaps.straightCollar bentCollar motion motion).isotopy.frame
      halfway (1 / 3, 3 / 4) = _
    rw [matchCaps.glueWithMotions_upper _ _ _ _ _ _ (by norm_num)]
    change (1 / 3 + displacement halfway (slabHeight 1 (3 / 4)),
      halfHeight 1 (slabHeight 1 (3 / 4))) = _
    norm_num [displacement, tent, halfway, slabHeight, halfHeight]
  · rw [← middle_mid, Homeomorph.symm_apply_apply]

example (t : Time) (x : ℝ) :
    combined.isotopy.frame t (x, 1 / 4) = (x, 1 / 4) ∧
    combined.isotopy.frame t (x, 1 / 2) = (x, 1 / 2) :=
  ⟨matchCaps.glueWithMotions_lower_splice _ _ _ _ t x, matchCaps.glueWithMotions_upper_splice _ _ _ _ t x⟩

/-- The moving collar midpoint lies on the actual renamed composite wire. -/
example :
    (combined.drawing halfway).x ((combined.correspondence halfway).rename
      (matchCaps.gluedCollarId middleId)) (3 / 8) = 5 / 12 := by
  let source := matchCaps.glueWith matchCaps.straightCollar
  let w := matchCaps.gluedCollarId middleId
  have x : source.x w (3 / 8) = 1 / 3 := by
    change (matchCaps.glueWith matchCaps.straightCollar).x (matchCaps.gluedCollarId middleId) (3 / 8) = _
    rw [matchCaps.glueWith_x_collar _ _ (by norm_num [Set.mem_Icc]), matchCaps.straightCollar_x,
      collar_bottom_third, collar_top_third]
    norm_num [interpolate]
  have h := (combined.correspondence halfway).wire w (3 / 8)
    (wire_covers source w _ (by norm_num [Set.mem_Icc]))
  change combined.isotopy.frame halfway (source.x w (3 / 8), 3 / 8) = _ at h
  rw [x, middle_mid] at h
  exact (congrArg Prod.fst h).symm

example :
    combined.isotopy.frame halfway '' ((matchCaps.glueWith matchCaps.straightCollar).wire
        (matchCaps.gluedCollarId middleId)).trace =
      ((combined.drawing halfway).wire ((combined.correspondence halfway).rename
        (matchCaps.gluedCollarId middleId))).trace :=
  matchCaps.glueWithMotions_trace _ _ _ _ halfway _

private noncomputable def oneContact : CapProfile Bool where
  size := 1
  label _ := true
  x _ := 1 / 3
  ordered := by
    intro i j h
    exact (lt_irrefl i ((Subsingleton.elim j i) ▸ h)).elim

private noncomputable def fixedFrame (t : Time) : FixedDrawing signature oneContact oneContact where
  vertices := 0
  wires := 1
  drawing := drawing t
  input :=
    { toFun := fun w => ⟨w, rfl⟩
      invFun := Subtype.val
      left_inv _ := rfl
      right_inv _ := Subtype.ext rfl }
  output :=
    { toFun := fun w => ⟨w, rfl⟩
      invFun := Subtype.val
      left_inv _ := rfl
      right_inv _ := Subtype.ext rfl }
  input_label _ := rfl
  output_label _ := rfl
  input_x _ := by
    change 1 / 3 + displacement t 0 = 1 / 3
    norm_num [displacement, tent]
  output_x _ := by
    change 1 / 3 + displacement t 1 = 1 / 3
    norm_num [displacement, tent]

private noncomputable def beginning : Time := ⟨0, le_rfl, zero_le_one⟩

private theorem bend_equivalent (t : Time) : (fixedFrame beginning).Equivalent (fixedFrame t) :=
  ⟨ProgressiveGraph.Diagram.CapComparison.ofMotion motion t⟩

/-- A bend in only the lower operand gives the same class after gluing. -/
example :
    (CapClass.ofDrawing (fixedFrame beginning)).thenDo (CapClass.ofDrawing (fixedFrame beginning)) =
      (CapClass.ofDrawing (fixedFrame halfway)).thenDo (CapClass.ofDrawing (fixedFrame beginning)) := by
  rw [CapClass.thenDo_drawings, CapClass.thenDo_drawings]
  exact CapClass.sound (FixedDrawing.thenDo_congr (bend_equivalent halfway)
    (FixedDrawing.Equivalent.refl _))

/-- Three actual collared operands define the same class under the two
parenthesizations, with the bent middle frame kept at its fixed contacts. -/
example :
    ((CapClass.ofDrawing (fixedFrame beginning)).thenDo (CapClass.ofDrawing (fixedFrame halfway))).thenDo
      (CapClass.ofDrawing (fixedFrame beginning)) =
    (CapClass.ofDrawing (fixedFrame beginning)).thenDo
      ((CapClass.ofDrawing (fixedFrame halfway)).thenDo (CapClass.ofDrawing (fixedFrame beginning))) :=
  CapClass.thenDo_assoc _ _ _

private theorem oneContact_inside : oneContact.Inside := by
  intro i
  change (1 / 3 : ℝ) ∈ Set.Ioo 0 1
  norm_num

example : (fixedFrame halfway).drawing.x (0 : Fin 1) (1 / 2) = 5 / 12 := by
  change (1 / 3 : ℝ) + displacement halfway (1 / 2) = 5 / 12
  norm_num [displacement, halfway, tent]

/-- Both units act on the class of the genuinely bent strand. -/
example :
    (CapClass.identity signature oneContact oneContact_inside).thenDo
      (CapClass.ofDrawing (fixedFrame halfway)) = CapClass.ofDrawing (fixedFrame halfway) ∧
    (CapClass.ofDrawing (fixedFrame halfway)).thenDo
      (CapClass.identity signature oneContact oneContact_inside) = CapClass.ofDrawing (fixedFrame halfway) :=
  ⟨CapClass.identity_thenDo _ _, CapClass.thenDo_identity _ _⟩

private noncomputable def emptyUnit :=
  CapClass.identity signature CapProfile.empty CapProfile.empty_inside

example : emptyUnit.thenDo emptyUnit = emptyUnit :=
  CapClass.identity_thenDo _ CapProfile.empty_inside

open CategoryTheory

private noncomputable def capObject : FixedCap signature := ⟨oneContact, oneContact_inside⟩

private noncomputable def bentMap (t : Time) : capObject ⟶ capObject :=
  FixedCap.ofDrawing (fixedFrame t)

example : (fixedFrame lastTime).drawing.x (0 : Fin 1) (1 / 2) = 1 / 2 := by
  change (1 / 3 : ℝ) + displacement lastTime (1 / 2) = 1 / 2
  norm_num [displacement, lastTime, tent]

example :
    𝟙 capObject ≫ bentMap halfway = bentMap halfway ∧
      bentMap lastTime ≫ 𝟙 capObject = bentMap lastTime :=
  ⟨Category.id_comp _, Category.comp_id _⟩

example :
    (bentMap halfway ≫ bentMap lastTime) ≫ bentMap halfway =
      bentMap halfway ≫ (bentMap lastTime ≫ bentMap halfway) :=
  Category.assoc _ _ _

example :
    bentMap halfway ≫ bentMap lastTime =
      FixedCap.ofDrawing ((fixedFrame halfway).thenDo (fixedFrame lastTime)) :=
  FixedCap.comp_drawings _ _

example (h : oneContact.Inside) :
    (𝟙 capObject : capObject ⟶ capObject) =
      FixedCap.ofDrawing (FixedDrawing.identity signature oneContact h) :=
  FixedCap.id_eq capObject h

example :
    𝟙 (FixedCap.empty signature) ≫ 𝟙 (FixedCap.empty signature) =
      𝟙 (FixedCap.empty signature) :=
  Category.id_comp _

end Silmaril.RuntimeWires.Proofs.OperandAmbient.Regression
