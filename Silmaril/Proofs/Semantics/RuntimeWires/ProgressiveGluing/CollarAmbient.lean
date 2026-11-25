module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarMotion
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CollarAmbient

open ProgressiveGraph PolygonalCollar OrderedKnots

universe u
variable {O : Type u} {W : ℕ} {cap : CollarSpec O W}

noncomputable def capImage (cap : CollarSpec O W) : Finset ℝ := Finset.univ.image cap.bottom

theorem capImage_card (cap : CollarSpec O W) : (capImage cap).card = W := by
  rw [capImage, Finset.card_image_of_injective _ cap.bottom_injective, Finset.card_univ, Fintype.card_fin]

noncomputable def capNumber (cap : CollarSpec O W) : Fin W ≃ capImage cap :=
  Equiv.ofBijective (fun w => ⟨cap.bottom w, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    ⟨fun _ _ h => cap.bottom_injective (congrArg Subtype.val h), fun z => by
      obtain ⟨w, _, eq⟩ := Finset.mem_image.mp z.property
      exact ⟨w, Subtype.ext eq⟩⟩

/-- Keep one order of wire IDs for all times and heights. -/
noncomputable def capOrder (cap : CollarSpec O W) : Fin W ≃ Fin W :=
  ((capImage cap).orderIsoOfFin (capImage_card cap)).toEquiv.trans (capNumber cap).symm

theorem capOrder_strict (cap : CollarSpec O W) : StrictMono (cap.bottom ∘ capOrder cap) := by
  intro i j h
  change (capNumber cap (capOrder cap i)).val < (capNumber cap (capOrder cap j)).val
  simp only [capOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact ((capImage cap).orderIsoOfFin (capImage_card cap)).strictMono h

/-- Extend the wire coordinates by the two fixed sides of the square. -/
noncomputable def knots (p : PolygonalCollar cap) (h : Time) : Fin (W + 2) → ℝ :=
  Fin.snoc (Fin.cons 0 fun i => (p.wire (capOrder cap i)).x h.val) 1

theorem knots_zero (p : PolygonalCollar cap) (h : Time) : knots p h 0 = 0 := by
  simp [knots]

theorem knots_last (p : PolygonalCollar cap) (h : Time) : knots p h (Fin.last (W + 1)) = 1 := by
  simp [knots]

theorem knots_wire (p : PolygonalCollar cap) (h : Time) (i : Fin W) :
    knots p h i.succ.castSucc = (p.wire (capOrder cap i)).x h.val := by
  simp only [knots, Fin.snoc_castSucc, Fin.cons_succ]

theorem knots_strict (p : PolygonalCollar cap) (h : Time) : StrictMono (knots p h) := by
  let x (i : Fin W) := (p.wire (capOrder cap i)).x h.val
  have allInside (i : Fin W) := p.inside (capOrder cap i) h.val h.property
  have first : StrictMono (Fin.cons 0 x) :=
    Fin.strictMono_cons.mpr ⟨fun i => (allInside i).1,
      fun _ _ lt => p.ordered _ _ _ h.property (capOrder_strict cap lt)⟩
  change StrictMono (Fin.snoc (Fin.cons 0 x) 1)
  intro i j lt
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact (lt_irrefl _ lt).elim
    | cast i =>
      rw [Fin.snoc_castSucc, Fin.snoc_last]
      induction i using Fin.cases with
      | zero => simpa only [Fin.cons_zero] using (zero_lt_one : (0 : ℝ) < 1)
      | succ i => exact (allInside i).2
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact ((Fin.le_last j.castSucc).not_gt lt).elim
    | cast i =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact first (Fin.castSucc_lt_castSucc_iff.mp lt)

noncomputable def lowerCap : Time := ⟨0, le_rfl, zero_le_one⟩
noncomputable def upperCap : Time := ⟨1, zero_le_one, le_rfl⟩

theorem knots_same_at_cap (p q : PolygonalCollar cap) (h : Time)
    (capHeight : h = lowerCap ∨ h = upperCap) : knots p h = knots q h := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [knots_last, knots_last]
  | cast i =>
    induction i using Fin.cases with
    | zero => rw [show (0 : Fin (W + 1)).castSucc = 0 from rfl, knots_zero, knots_zero]
    | succ i =>
      rw [knots_wire, knots_wire]
      rcases capHeight with rfl | rfl
      · exact (p.bottom _).trans (q.bottom _).symm
      · exact (p.top _).trans (q.top _).symm

/-- Read normalized collar height, clamping to the nearest cap outside the slab. -/
noncomputable def height (y : ℝ) : Time :=
  ⟨max 0 (min 1 (4 * y - 1)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem height_inside {y : ℝ} (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (height y).val = 4 * y - 1 := by
  change max 0 (min 1 (4 * y - 1)) = _
  rw [min_eq_right (by linarith [hy.2]), max_eq_right (by linarith [hy.1])]

theorem height_outside {y : ℝ} (h : y ≤ 1 / 4 ∨ 1 / 2 ≤ y) :
    height y = lowerCap ∨ height y = upperCap := by
  rcases h with low | high
  · left
    apply Subtype.ext
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  · right
    apply Subtype.ext
    change max 0 (min 1 (4 * y - 1)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem continuous_height : Continuous height := by
  apply Continuous.subtype_mk
  change Continuous (fun y : ℝ => max 0 (min 1 (4 * y - 1)))
  fun_prop

variable (p q : PolygonalCollar cap)

noncomputable def sourceKnots (z : Time × (ℝ × ℝ)) := knots p (height z.2.2)
noncomputable def movingKnots (z : Time × (ℝ × ℝ)) := knots (p.blend q z.1) (height z.2.2)

theorem continuous_knots {P : Type*} [TopologicalSpace P] {h : P → Time}
    {c : P → PolygonalCollar cap} (hc : ∀ w, Continuous (fun z => ((c z).wire w).x (h z).val))
    (i : Fin (W + 2)) : Continuous (fun z => knots (c z) (h z) i) := by
  induction i using Fin.lastCases with
  | last => simpa only [knots_last] using (continuous_const : Continuous fun _ : P => (1 : ℝ))
  | cast i =>
    induction i using Fin.cases with
    | zero =>
      simpa only [show (0 : Fin (W + 1)).castSucc = 0 from rfl, knots_zero] using
        (continuous_const : Continuous fun _ : P => (0 : ℝ))
    | succ i => simpa only [knots_wire] using hc (capOrder cap i)

theorem continuous_source (i : Fin (W + 2)) :
    Continuous (fun z => sourceKnots p z i) :=
  continuous_knots (fun w => ((p.wire w).continuous.domRestrict).comp
    (continuous_height.comp (continuous_snd.comp continuous_snd))) i

theorem continuous_moving (i : Fin (W + 2)) :
    Continuous (fun z => movingKnots p q z i) :=
  continuous_knots (fun w => (continuous_fst.comp
    ((p.blend_continuous q w).comp (continuous_fst.prodMk
      (continuous_height.comp (continuous_snd.comp continuous_snd)))))) i

/-- Coordinate formula on the entire plane. -/
noncomputable def frame (t : Time) (z : ℝ × ℝ) : ℝ × ℝ :=
  (transfer (sourceKnots p (t, z)) (movingKnots p q (t, z)) z.1, z.2)

noncomputable def inverseFrame (t : Time) (z : ℝ × ℝ) : ℝ × ℝ :=
  (transfer (movingKnots p q (t, z)) (sourceKnots p (t, z)) z.1, z.2)

theorem frame_continuous : Continuous (fun z : Time × (ℝ × ℝ) => frame p q z.1 z.2) :=
  (continuous_transfer (continuous_source p) (continuous_moving p q)
    (fun _ => knots_strict _ _) (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)

theorem inverse_continuous : Continuous (fun z : Time × (ℝ × ℝ) => inverseFrame p q z.1 z.2) :=
  (continuous_transfer (continuous_moving p q) (continuous_source p)
    (fun _ => knots_strict _ _) (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)

noncomputable def ambient (t : Time) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := frame p q t
  invFun := inverseFrame p q t
  left_inv z := Prod.ext (transfer_inverse (knots_strict _ _) (knots_strict _ _) z.1) rfl
  right_inv z := Prod.ext (transfer_inverse (knots_strict _ _) (knots_strict _ _) z.1) rfl
  continuous_toFun := (frame_continuous p q).comp (continuous_const.prodMk continuous_id)
  continuous_invFun := (inverse_continuous p q).comp (continuous_const.prodMk continuous_id)

theorem ambient_zero (z : ℝ × ℝ) : ambient p q lowerCap z = z := by
  change (transfer (knots p (height z.2)) (knots (p.blend q lowerCap) (height z.2)) z.1, z.2) = z
  rw [show p.blend q lowerCap = p from p.blend_zero q]
  exact Prod.ext (transfer_self (knots_strict _ _) _) rfl

theorem ambient_outside (t : Time) (z : ℝ × ℝ) (h : z.2 ≤ 1 / 4 ∨ 1 / 2 ≤ z.2) :
    ambient p q t z = z := by
  change (transfer (knots p (height z.2)) (knots (p.blend q t) (height z.2)) z.1, z.2) = z
  rw [knots_same_at_cap (p.blend q t) p _ (height_outside h)]
  exact Prod.ext (transfer_self (knots_strict _ _) _) rfl

theorem ambient_outside_sides (t : Time) (z : ℝ × ℝ) (h : z.1 ≤ 0 ∨ 1 ≤ z.1) :
    ambient p q t z = z := by
  change (transfer (knots p (height z.2)) (knots (p.blend q t) (height z.2)) z.1, z.2) = z
  refine Prod.ext ?_ (rfl : z.2 = z.2)
  change transfer (knots p (height z.2)) (knots (p.blend q t) (height z.2)) z.1 = z.1
  rcases h with low | high
  · rw [transfer_left (knots_strict _ _) (by rwa [knots_zero]), knots_zero, knots_zero,
      sub_zero, zero_add]
  · rw [transfer_right (knots_strict _ _) (by rwa [knots_last]), knots_last, knots_last]
    linarith

theorem ambient_increasing (t : Time) (y : ℝ) :
    StrictMono (fun x => (ambient p q t (x, y)).1) := by
  change StrictMono (transfer (knots p (height y)) (knots (p.blend q t) (height y)))
  exact transfer_strictMono (knots_strict p (height y)) (knots_strict (p.blend q t) (height y))

theorem ambient_wire (t : Time) (w : Fin W) {y : ℝ} (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    ambient p q t ((p.wire w).x (4 * y - 1), y) = (((p.blend q t).wire w).x (4 * y - 1), y) := by
  let i := (capOrder cap).symm w
  have eq : capOrder cap i = w := Equiv.apply_symm_apply _ _
  have wire (c : PolygonalCollar cap) : knots c (height y) i.succ.castSucc = (c.wire w).x (4 * y - 1) := by
    rw [knots_wire, eq, height_inside hy]
  change (transfer (knots p (height y)) (knots (p.blend q t) (height y)) ((p.wire w).x (4 * y - 1)), y) = _
  exact Prod.ext ((congrArg (transfer (knots p (height y)) (knots (p.blend q t) (height y)))
    (wire p).symm).trans ((transfer_knot (knots_strict p (height y)) i.succ.castSucc).trans
      (wire (p.blend q t)))) rfl

end Silmaril.RuntimeWires.Proofs.CollarAmbient
