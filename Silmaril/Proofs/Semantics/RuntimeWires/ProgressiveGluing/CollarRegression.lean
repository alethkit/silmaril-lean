module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarMotion
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing.CollarRegression

open ProgressiveGraph

private abbrev signature : Signature Bool where
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

private noncomputable def leftX (i : Fin 2) : ℝ := if i = 0 then 1 / 6 else 1 / 2
private noncomputable def rightX (i : Fin 2) : ℝ := if i = 0 then 5 / 6 else 1 / 3

private noncomputable def operand (side : Bool) : CollarSpec Bool 2 where
  label i := if side then decide (i = 0) else decide (i = 1)
  bottom := if side then rightX else leftX
  top := if side then rightX else leftX
  bottom_inside := by intro i; cases side <;> fin_cases i <;> norm_num [leftX, rightX, Set.mem_Ioo]
  top_inside := by intro i; cases side <;> fin_cases i <;> norm_num [leftX, rightX, Set.mem_Ioo]
  bottom_injective := by
    intro i j h
    cases side <;> fin_cases i <;> fin_cases j <;> norm_num [leftX, rightX] at *
  order _ _ := Iff.rfl

private noncomputable def lower := (operand false).drawing signature
private noncomputable def upper := (operand true).drawing signature

private noncomputable def leftCap (i : Fin 2) : Diagram.PartialVerticalMatch.Contact lower :=
  ⟨i, (operand false).drawing_finish i⟩

private noncomputable def rightCap (i : Fin 2) : {w : Fin 2 // upper.start w = none} :=
  ⟨i, (operand true).drawing_start i⟩

private def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

private noncomputable def matched : lower.OrderedVerticalMatch upper where
  contact :=
    { toFun := fun w => rightCap (swap w.val)
      invFun := fun w => leftCap (swap w.val)
      left_inv := fun _ => Subtype.ext (Equiv.swap_apply_self _ _ _)
      right_inv := fun _ => Subtype.ext (Equiv.swap_apply_self _ _ _) }
  label w := by
    change ((operand false).drawing signature).label w.val =
      ((operand true).drawing signature).label (swap w.val)
    rw [CollarSpec.drawing_label, CollarSpec.drawing_label]
    obtain ⟨w, _⟩ := w
    fin_cases w <;> rfl
  order a b := by
    change ((operand false).drawing signature).x a.val 1 < ((operand false).drawing signature).x b.val 1 ↔
      ((operand true).drawing signature).x (swap a.val) 0 < ((operand true).drawing signature).x (swap b.val) 0
    rw [CollarSpec.drawing_top, CollarSpec.drawing_top, CollarSpec.drawing_bottom, CollarSpec.drawing_bottom]
    obtain ⟨a, _⟩ := a
    obtain ⟨b, _⟩ := b
    have inv₀ : swap 0 = 1 := Equiv.swap_apply_left _ _
    have inv₁ : swap 1 = 0 := Equiv.swap_apply_right _ _
    fin_cases a <;> fin_cases b <;> norm_num [operand, leftX, rightX, inv₀, inv₁]

private noncomputable def first := Diagram.OrderedVerticalMatch.collarIndex lower (leftCap 0)
private noncomputable def second := Diagram.OrderedVerticalMatch.collarIndex lower (leftCap 1)

private theorem first_x (y : ℝ) : matched.collar.x first y = interpolate (1 / 6) (1 / 3) y := by
  rw [first, matched.collar_x]
  change interpolate ((operand false).drawing signature |>.x 0 1)
    ((operand true).drawing signature |>.x (swap 0) 0) y = _
  rw [CollarSpec.drawing_top, CollarSpec.drawing_bottom, show swap 0 = 1 from Equiv.swap_apply_left _ _]
  rfl

private theorem second_x (y : ℝ) : matched.collar.x second y = interpolate (1 / 2) (5 / 6) y := by
  rw [second, matched.collar_x]
  change interpolate ((operand false).drawing signature |>.x 1 1)
    ((operand true).drawing signature |>.x (swap 1) 0) y = _
  rw [CollarSpec.drawing_top, CollarSpec.drawing_bottom, show swap 1 = 0 from Equiv.swap_apply_right _ _]
  rfl

/-- The endpoint spacings differ. Both strands retain their order and
interpolate to these exact points at the collar midpoint. -/
example : (matched.collar.x first (1 / 2), matched.collar.x second (1 / 2)) = (1 / 4, 2 / 3) := by
  rw [first_x, second_x]
  norm_num [interpolate]

/-- The first strand reaches the same midpoint after placement in the
actual composite collar slab. -/
example : matched.glue.x (matched.upperJoin.upperId (matched.contact (leftCap 0)).val) (3 / 8) = 1 / 4 := by
  rw [matched.glue_x_in_collar (leftCap 0) (by norm_num [Set.mem_Icc]),
    show (4 * (3 / 8 : ℝ) - 1) = 1 / 2 by norm_num, ← matched.collar_x]
  change matched.collar.x first (1 / 2) = _
  rw [first_x]
  norm_num [interpolate]

private noncomputable def collarRead := matched.collar.layerSweep

private theorem lowerOrdered :
    ([leftCap 0, leftCap 1]).Pairwise (fun a b => lower.x a.val 1 < lower.x b.val 1) := by
  simp [List.pairwise_cons]
  change ((operand false).drawing signature).x 0 1 < ((operand false).drawing signature).x 1 1
  rw [CollarSpec.drawing_top, CollarSpec.drawing_top]
  norm_num [operand, leftX]

private theorem allContacts (w : Diagram.PartialVerticalMatch.Contact lower) : w ∈ [leftCap 0, leftCap 1] := by
  obtain ⟨i, h⟩ := w
  fin_cases i
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

example : collarRead.word 0 = [false, true] := by
  have active := (matched.collar.level_gap_regular (collarRead.cuts.in_gap 0)).1
  have ids := Diagram.ordered_cut_unique (collarRead.ordered 0)
    (matched.collar_ordered_cut allContacts lowerOrdered active)
  rw [Diagram.LayerSweep.word, ids]
  change [matched.collar.label first, matched.collar.label second] = _
  rw [first, second, matched.collar_label, matched.collar_label]
  exact congrArg₂ List.cons ((operand false).drawing_label 0) (congrArg List.singleton ((operand false).drawing_label 1))

example : collarRead.sheet.reindex rfl (matched.collar_word collarRead) = Sliced.Sheet.empty (collarRead.word 0) :=
  matched.collar_identity collarRead

private noncomputable def lowerRead := lower.layerSweep
private noncomputable def upperRead := upper.layerSweep
private noncomputable def fullRead := matched.glue.layerSweep

example :
    fullRead.sheet.reindex (matched.sweep_first_word lowerRead fullRead) (matched.sweep_last_word upperRead fullRead) =
      lowerRead.sheet.thenDo (upperRead.sheet.reindex (matched.sweep_join_word lowerRead upperRead) rfl) :=
  matched.sweep_concat lowerRead upperRead fullRead

private abbrev CapId := Fin (Diagram.OrderedVerticalMatch.collarCount lower)

private noncomputable def knot (i : CapId) : ℝ :=
  interpolate (matched.collarSpec.bottom i) (matched.collarSpec.top i) (3 / 4)

private theorem knot_inside (i : CapId) : knot i ∈ Set.Ioo 0 1 :=
  interpolate_inside (matched.collarSpec.bottom_inside i) (matched.collarSpec.top_inside i) (by
    norm_num [Set.mem_Icc])

private theorem knot_order {i j : CapId} (h : matched.collarSpec.bottom i < matched.collarSpec.bottom j) :
    knot i < knot j :=
  interpolate_lt h ((matched.collarSpec.order i j).mp h) (by norm_num [Set.mem_Icc])

private noncomputable def bendHalf (top : Bool) : CollarSpec Bool (Diagram.OrderedVerticalMatch.collarCount lower) where
  label := matched.collarSpec.label
  bottom := if top then knot else matched.collarSpec.bottom
  top := if top then matched.collarSpec.top else knot
  bottom_inside := by cases top; exacts [matched.collarSpec.bottom_inside, knot_inside]
  top_inside := by cases top; exacts [knot_inside, matched.collarSpec.top_inside]
  bottom_injective := by
    cases top
    · exact matched.collarSpec.bottom_injective
    · intro i j eq
      by_contra ne
      rcases lt_or_gt_of_ne (fun h => ne (matched.collarSpec.bottom_injective h)) with h | h
      · exact (knot_order h).ne eq
      · exact (knot_order h).ne' eq
  order i j := by
    have h : knot i < knot j ↔ matched.collarSpec.bottom i < matched.collarSpec.bottom j := by
      simpa only [knot] using collar_order matched.collarSpec (a := i) (b := j)
        (hy := (by norm_num [Set.mem_Icc] : (3 / 4 : ℝ) ∈ Set.Icc 0 1))
    cases top
    · exact h.symm
    · exact h.trans (matched.collarSpec.order i j)

private noncomputable def bentLeft (w : CapId) : Wire 0 (1 / 2) :=
  ((collarWire (bendHalf false) w).halve 0).atBounds
    (by norm_num [halfHeight]) (by norm_num [halfHeight])

private noncomputable def bentRight (w : CapId) : Wire (1 / 2) 1 :=
  ((collarWire (bendHalf true) w).halve 1).atBounds
    (by norm_num [halfHeight]) (by norm_num [halfHeight])

private theorem bent_contact (w : CapId) : (bentLeft w).x (1 / 2) = (bentRight w).x (1 / 2) := by
  change interpolate (matched.collarSpec.bottom w) (knot w) (slabHeight 0 (1 / 2)) =
    interpolate (knot w) (matched.collarSpec.top w) (slabHeight 1 (1 / 2))
  norm_num [slabHeight, interpolate]

private noncomputable def bentWire (w : CapId) : Wire 0 1 :=
  (bentLeft w).splice (bentRight w) (bent_contact w)

private theorem bent_low (w : CapId) {y : ℝ} (h : y ≤ 1 / 2) :
    (bentWire w).x y = interpolate (matched.collarSpec.bottom w) (knot w) (slabHeight 0 y) :=
  (bentLeft w).splice_x_lower (bentRight w) (bent_contact w) h

private theorem bent_high (w : CapId) {y : ℝ} (h : 1 / 2 ≤ y) :
    (bentWire w).x y = interpolate (knot w) (matched.collarSpec.top w) (slabHeight 1 y) :=
  (bentLeft w).splice_x_upper (bentRight w) (bent_contact w) h

private noncomputable def bent : PolygonalCollar matched.collarSpec where
  wire := bentWire
  bottom w := by rw [bent_low w (by norm_num)]; norm_num [interpolate, slabHeight]
  top w := by rw [bent_high w (by norm_num)]; norm_num [interpolate, slabHeight]
  inside w y hy := by
    rcases le_total y (1 / 2) with low | high
    · rw [bent_low w low]
      exact interpolate_inside (matched.collarSpec.bottom_inside w) (knot_inside w)
        ⟨by unfold slabHeight; linarith [hy.1], by unfold slabHeight; linarith⟩
    · rw [bent_high w high]
      exact interpolate_inside (knot_inside w) (matched.collarSpec.top_inside w)
        ⟨by unfold slabHeight; linarith, by unfold slabHeight; linarith [hy.2]⟩
  ordered i j y hy h := by
    rcases le_total y (1 / 2) with low | high
    · rw [bent_low i low, bent_low j low]
      exact interpolate_lt h (knot_order h)
        ⟨by unfold slabHeight; linarith [hy.1], by unfold slabHeight; linarith⟩
    · rw [bent_high i high, bent_high j high]
      exact interpolate_lt (knot_order h) ((matched.collarSpec.order i j).mp h)
        ⟨by unfold slabHeight; linarith, by unfold slabHeight; linarith [hy.2]⟩

private noncomputable def halfTime : PolygonalCollar.Time := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem straight_first (t : ℝ) :
    (matched.straightCollar.wire first).x t = interpolate (1 / 6) (1 / 3) t := by
  rw [matched.straightCollar_x, first, matched.collarSpec_bottom, matched.collarSpec_top,
    Equiv.symm_apply_apply]
  exact (matched.collar_x (leftCap 0) t).symm.trans (first_x t)

private theorem straight_second (t : ℝ) :
    (matched.straightCollar.wire second).x t = interpolate (1 / 2) (5 / 6) t := by
  rw [matched.straightCollar_x, second, matched.collarSpec_bottom, matched.collarSpec_top,
    Equiv.symm_apply_apply]
  exact (matched.collar_x (leftCap 1) t).symm.trans (second_x t)

private theorem moving_mid (w : CapId) :
    (((matched.straightCollar.blend bent halfTime).wire w).x (1 / 2)) =
      interpolate ((matched.straightCollar.wire w).x (1 / 2))
        ((matched.straightCollar.wire w).x (3 / 4)) (1 / 2) := by
  rw [PolygonalCollar.blend_x]
  change interpolate ((matched.straightCollar.wire w).x (1 / 2)) (bentWire w |>.x (1 / 2)) _ = _
  rw [bent_low w (by norm_num)]
  simp only [matched.straightCollar_x]
  norm_num [knot, slabHeight, interpolate, halfTime]

/-- Both strands move. Read the two exact coordinates at the midpoint of
the collar slab and at the midpoint of time. -/
example :
    ((matched.glueWith (matched.straightCollar.blend bent halfTime)).x (matched.gluedCollarId first) (3 / 8),
      (matched.glueWith (matched.straightCollar.blend bent halfTime)).x (matched.gluedCollarId second) (3 / 8)) =
    (13 / 48, 17 / 24) := by
  rw [matched.glueWith_x_collar _ first (by norm_num [Set.mem_Icc]),
    matched.glueWith_x_collar _ second (by norm_num [Set.mem_Icc]),
    show 4 * (3 / 8 : ℝ) - 1 = 1 / 2 by norm_num, moving_mid, moving_mid,
    straight_first, straight_first, straight_second, straight_second]
  norm_num [interpolate]

/-- At both composite splice heights, the actual contacts are fixed at
every time, including times 0 and 1. -/
example (t : PolygonalCollar.Time) (w : CapId) :
    ((matched.glueWith (matched.straightCollar.blend bent t)).x (matched.gluedCollarId w) (1 / 4),
      (matched.glueWith (matched.straightCollar.blend bent t)).x (matched.gluedCollarId w) (1 / 2)) =
    (matched.collarSpec.bottom w, matched.collarSpec.top w) := by
  rw [matched.glueWith_x_collar _ w (by norm_num [Set.mem_Icc]),
    matched.glueWith_x_collar _ w (by norm_num [Set.mem_Icc]),
    show 4 * (1 / 4 : ℝ) - 1 = 0 by norm_num, show 4 * (1 / 2 : ℝ) - 1 = 1 by norm_num,
    PolygonalCollar.bottom, PolygonalCollar.top]

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing.CollarRegression
