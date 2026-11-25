module

public import Silmaril.Proofs.Semantics.RuntimeWires.PolygonalSwap.Vertical
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalSwap

open Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {floor : ℝ} {e f : S.Edge}

private theorem ramp_range (a b x : ℝ) : BoxPair.ramp a b x ∈ Set.Icc 0 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private theorem ramp_zero {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    BoxPair.ramp a b x = 0 := by
  unfold BoxPair.ramp
  have h := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hab.le)
  exact max_eq_left ((min_le_right _ _).trans h)

private theorem ramp_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    BoxPair.ramp a b x = 1 := by
  unfold BoxPair.ramp
  rw [min_eq_left ((one_le_div (sub_pos.mpr hab)).mpr (sub_le_sub_right hx _)),
    max_eq_right zero_le_one]

variable (d : BoxPair S floor e f)

private theorem leftSide_lt : d.leftSide < d.first.left := by
  unfold BoxPair.leftSide
  linarith

private theorem lt_rightSide : d.second.right < d.rightSide := by
  unfold BoxPair.rightSide
  linarith

theorem altitude_range (t : SwapTime) (x : ℝ) : d.altitude t x ∈ BoxAltitude := by
  let a := BoxPair.ramp d.leftSide d.first.left x
  let b := BoxPair.ramp d.first.right d.second.left x
  let c := BoxPair.ramp d.second.right d.rightSide x
  have ha : a ∈ Set.Icc (0 : ℝ) 1 := ramp_range _ _ _
  have hb : b ∈ Set.Icc (0 : ℝ) 1 := ramp_range _ _ _
  have hc : c ∈ Set.Icc (0 : ℝ) 1 := ramp_range _ _ _
  have hl := (BoxPair.firstAltitude t).property
  have hr := (BoxPair.secondAltitude t).property
  let l := (BoxPair.firstAltitude t).val - 1
  let r := (BoxPair.secondAltitude t).val - 1
  have hl0 : 0 ≤ l := sub_nonneg.mpr hl.1
  have hr0 : 0 ≤ r := sub_nonneg.mpr hr.1
  have hl3 : l ≤ 3 := by dsimp [l]; linarith [hl.2]
  have hr3 : r ≤ 3 := by dsimp [r]; linarith [hr.2]
  have hnb := sub_nonneg.mpr hb.2
  have hnc := sub_nonneg.mpr hc.2
  change (1 : ℝ) ≤ 1 + l * a * (1 - b) + r * b * (1 - c) ∧
    1 + l * a * (1 - b) + r * b * (1 - c) ≤ 4
  constructor
  · linarith [mul_nonneg (mul_nonneg hl0 ha.1) hnb, mul_nonneg (mul_nonneg hr0 hb.1) hnc]
  · have hleft : l * a * (1 - b) ≤ 3 * (1 - b) :=
      mul_le_mul_of_nonneg_right ((mul_le_of_le_one_right hl0 ha.2).trans hl3) hnb
    have hright : r * b * (1 - c) ≤ 3 * b :=
      (mul_le_of_le_one_right (mul_nonneg hr0 hb.1) (sub_le_self _ hc.1)).trans
        (mul_le_mul_of_nonneg_right hr3 hb.1)
    linarith

theorem altitude_first (t : SwapTime) {x : ℝ} (hx : x ∈ Set.Icc d.first.left d.first.right) :
    d.altitude t x = (BoxPair.firstAltitude t).val := by
  simp only [BoxPair.altitude, ramp_one (leftSide_lt d) hx.1, ramp_zero d.second.left_bound hx.2]
  ring

theorem altitude_second (t : SwapTime) {x : ℝ} (hx : x ∈ Set.Icc d.second.left d.second.right) :
    d.altitude t x = (BoxPair.secondAltitude t).val := by
  simp only [BoxPair.altitude, ramp_one d.second.left_bound hx.1,
    ramp_zero (lt_rightSide d) hx.2]
  ring

private theorem altitude_leftSide (t : SwapTime) : d.altitude t d.leftSide = 1 := by
  have hs : d.leftSide ≤ d.first.right := (leftSide_lt d).le.trans d.first.width.le
  simp only [BoxPair.altitude, ramp_zero (leftSide_lt d) le_rfl, ramp_zero d.second.left_bound hs]
  ring

private theorem altitude_rightSide (t : SwapTime) : d.altitude t d.rightSide = 1 := by
  have hs : d.second.left ≤ d.rightSide := d.second.width.le.trans (lt_rightSide d).le
  simp only [BoxPair.altitude, ramp_one d.second.left_bound hs, ramp_one (lt_rightSide d) le_rfl]
  ring

theorem continuous_frame : Continuous (fun q : SwapTime × Point => d.frame q.1 q.2) := by
  unfold BoxPair.frame BoxPair.rescale BoxPair.altitude BoxPair.ramp
    BoxPair.firstAltitude BoxPair.secondAltitude
  dsimp
  fun_prop

theorem frame_fixed (t : SwapTime) {p : Point} (hp : d.OnBoundary p) : d.frame t p = p := by
  refine Prod.ext (by rfl) ?_
  change BoxPair.rescale (d.altitude t p.1) p.2 = p.2
  rcases hp with hx | hx | hy | hy
  · rw [hx, altitude_leftSide, rescale_identity]
  · rw [hx, altitude_rightSide, rescale_identity]
  · rw [hy, rescale_zero]
  · rw [hy, rescale_six]

theorem frame_vertical (t : SwapTime) (x : ℝ) :
    StrictMono (fun y => (d.frame t (x, y)).2) :=
  rescale_strict (altitude_range d t x)

private theorem frame_mem (t : SwapTime) {p : Point} (hp : p ∈ d.rectangle) :
    d.frame t p ∈ d.rectangle := by
  refine ⟨hp.1, ?_⟩
  refine ⟨?_, ?_⟩
  · exact (rescale_zero _).symm.trans_le ((frame_vertical d t p.1).monotone hp.2.1)
  · exact ((frame_vertical d t p.1).monotone hp.2.2).trans_eq (rescale_six _)

private noncomputable def frameOn (t : SwapTime) (p : d.rectangle) : d.rectangle :=
  ⟨d.frame t p, frame_mem d t p.property⟩

private theorem frameOn_bijective (t : SwapTime) : Function.Bijective (frameOn d t) := by
  constructor
  · intro p q he
    have h := congrArg Subtype.val he
    have hx : p.val.1 = q.val.1 := by
      have hx := congrArg Prod.fst h
      exact hx
    have hy := congrArg Prod.snd h
    change BoxPair.rescale (d.altitude t p.val.1) p.val.2 =
      BoxPair.rescale (d.altitude t q.val.1) q.val.2 at hy
    rw [← hx] at hy
    exact Subtype.ext (Prod.ext hx ((frame_vertical d t p.val.1).injective hy))
  · intro p
    have hi := rescale_image (altitude_range d t p.val.1) (by norm_num : (0 : ℝ) ≤ 6)
    rw [rescale_zero, rescale_six] at hi
    obtain ⟨y, hy, eq⟩ := hi.symm.subset p.property.2
    exact ⟨⟨(p.val.1, y), p.property.1, hy⟩, Subtype.ext (Prod.ext rfl eq)⟩

private theorem continuous_frameOn : Continuous (fun q : SwapTime × d.rectangle => frameOn d q.1 q.2) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_frame d).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

noncomputable def frameHomeomorph (t : SwapTime) : d.rectangle ≃ₜ d.rectangle :=
  letI : CompactSpace d.rectangle := (isCompact_iff_compactSpace (s := d.rectangle)).mp (isCompact_Icc.prod isCompact_Icc)
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (frameOn d t) (frameOn_bijective d t))
    ((continuous_frameOn d).comp (continuous_const.prodMk continuous_id))

theorem frameHomeomorph_val (t : SwapTime) (p : d.rectangle) :
    (frameHomeomorph d t p).val = d.frame t p := by
  unfold frameHomeomorph Continuous.homeoOfEquivCompactToT2 Equiv.ofBijective frameOn
  rfl

/-- Rebase the reference frames so that the deformation begins at the identity. -/
noncomputable def deformation (t : SwapTime) : d.rectangle ≃ₜ d.rectangle :=
  (frameHomeomorph d swapStart).symm.trans (frameHomeomorph d t)

theorem deformation_apply (t : SwapTime) (p : d.rectangle) :
    deformation d t p = frameHomeomorph d t ((frameHomeomorph d swapStart).symm p) := by
  rfl

theorem continuous_deformation :
    Continuous (fun q : SwapTime × d.rectangle => deformation d q.1 q.2) :=
  (continuous_frameOn d).comp
    (continuous_fst.prodMk ((frameHomeomorph d swapStart).symm.continuous.comp continuous_snd))

theorem continuous_deformation_inverse :
    Continuous (fun q : SwapTime × d.rectangle => (deformation d q.1).symm q.2) := by
  let : CompactSpace SwapTime := isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace d.rectangle :=
    (isCompact_iff_compactSpace (s := d.rectangle)).mp (isCompact_Icc.prod isCompact_Icc)
  let action : (SwapTime × d.rectangle) ≃ (SwapTime × d.rectangle) :=
    { toFun := fun q => (q.1, deformation d q.1 q.2)
      invFun := fun q => (q.1, (deformation d q.1).symm q.2)
      left_inv := fun q => Prod.ext (by rfl) ((deformation d q.1).symm_apply_apply q.2)
      right_inv := fun q => Prod.ext (by rfl) ((deformation d q.1).apply_symm_apply q.2) }
  let homeo := Continuous.homeoOfEquivCompactToT2 (f := action)
    (continuous_fst.prodMk (continuous_deformation d))
  exact continuous_snd.comp homeo.symm.continuous

theorem deformation_start (p : d.rectangle) : deformation d swapStart p = p :=
  (frameHomeomorph d swapStart).apply_symm_apply p

theorem deformation_fixed (t : SwapTime) (p : d.rectangle) (hp : d.OnBoundary p.val) :
    deformation d t p = p := by
  have fixed (s : SwapTime) : frameHomeomorph d s p = p := Subtype.ext (frame_fixed d s hp)
  have inv : (frameHomeomorph d swapStart).symm p = p :=
    (frameHomeomorph d swapStart).symm_apply_eq.mpr (fixed swapStart).symm
  change frameHomeomorph d t ((frameHomeomorph d swapStart).symm p) = p
  rw [inv, fixed]

theorem deformation_horizontal (t : SwapTime) (p : d.rectangle) :
    (deformation d t p).val.1 = p.val.1 := by
  have h := congrArg (fun q : d.rectangle => q.val.1)
    ((frameHomeomorph d swapStart).apply_symm_apply p)
  exact h

theorem deformation_fiber (t : SwapTime) (x : ℝ) :
    deformation d t '' {p : d.rectangle | p.val.1 = x} = {p : d.rectangle | p.val.1 = x} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (deformation_horizontal d t q).trans hq
  · intro hp
    obtain ⟨q, rfl⟩ := (deformation d t).surjective p
    exact ⟨q, (deformation_horizontal d t q).symm.trans hp, rfl⟩

theorem deformation_vertical (t : SwapTime) {p q : d.rectangle}
    (hx : p.val.1 = q.val.1) (hy : p.val.2 < q.val.2) :
    (deformation d t p).val.2 < (deformation d t q).val.2 := by
  let a := (frameHomeomorph d swapStart).symm p
  let b := (frameHomeomorph d swapStart).symm q
  have ha : d.frame swapStart a.val = p.val :=
    congrArg Subtype.val ((frameHomeomorph d swapStart).apply_symm_apply p)
  have hb : d.frame swapStart b.val = q.val :=
    congrArg Subtype.val ((frameHomeomorph d swapStart).apply_symm_apply q)
  have xa : a.val.1 = p.val.1 := by
    have h := congrArg Prod.fst ha
    exact h
  have xb : b.val.1 = q.val.1 := by
    have h := congrArg Prod.fst hb
    exact h
  have xab : a.val.1 = b.val.1 := xa.trans (hx.trans xb.symm)
  have h : BoxPair.rescale (d.altitude swapStart a.val.1) a.val.2 <
      BoxPair.rescale (d.altitude swapStart b.val.1) b.val.2 := by
    change (d.frame swapStart a.val).2 < (d.frame swapStart b.val).2
    rw [ha, hb]
    exact hy
  rw [← xab] at h
  have yab := (rescale_strict (altitude_range d swapStart a.val.1)).lt_iff_lt.mp h
  change BoxPair.rescale (d.altitude t a.val.1) a.val.2 <
    BoxPair.rescale (d.altitude t b.val.1) b.val.2
  rw [← xab]
  exact (rescale_strict (altitude_range d t a.val.1)) yab

end Silmaril.RuntimeWires.Proofs.PolygonalSwap
