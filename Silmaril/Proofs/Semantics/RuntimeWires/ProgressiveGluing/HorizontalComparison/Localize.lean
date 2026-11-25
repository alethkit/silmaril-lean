module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Splice
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.HorizontalComparison

open ProgressiveGraph ProgressiveGraph.OrderedKnots

def fibre (f : CapHomeomorph) (y x : ℝ) : ℝ := (f.plane (x, y)).1

def fibreInv (f : CapHomeomorph) (y x : ℝ) : ℝ := (f.plane.symm (x, f.height y)).1

theorem plane_eq (f : CapHomeomorph) (x y : ℝ) :
    f.plane (x, y) = (fibre f y x, f.height y) :=
  Prod.ext rfl (f.height_eq _)

theorem symm_height (f : CapHomeomorph) (z : ℝ × ℝ) :
    (f.plane.symm z).2 = f.height.symm z.2 := by
  apply f.height.injective
  rw [f.height.apply_symm_apply, ← f.height_eq, f.plane.apply_symm_apply]

theorem height_fixed (f : CapHomeomorph) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) : f.height y = y :=
  (f.height_eq (0, y)).symm.trans (congrArg Prod.snd (f.outside (0, y) h))

theorem fibre_fixed (f : CapHomeomorph) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) (x : ℝ) :
    fibre f y x = x :=
  congrArg Prod.fst (f.outside (x, y) h)

/-- Injective horizontal fibres retain their orientation from the fixed bottom cap. -/
theorem fibre_strict (f : CapHomeomorph) (y : ℝ) : StrictMono (fibre f y) := by
  intro a b ab
  let diff := fun y => fibre f y b - fibre f y a
  have continuousDiff : Continuous diff :=
    (f.plane.continuous.comp (continuous_const.prodMk continuous_id)).fst.sub
      (f.plane.continuous.comp (continuous_const.prodMk continuous_id)).fst
  have pos : 0 < diff 0 := by
    change 0 < fibre f 0 b - fibre f 0 a
    rw [fibre_fixed f (.inl le_rfl), fibre_fixed f (.inl le_rfl)]
    exact sub_pos.mpr ab
  by_contra! no
  have low : diff y ≤ 0 := sub_nonpos.mpr no
  obtain ⟨t, _, zero⟩ := intermediate_value_uIcc (a := 0) (b := y) continuousDiff.continuousOn
    (Set.mem_uIcc_of_ge low pos.le)
  have eq : fibre f t b = fibre f t a := sub_eq_zero.mp zero
  have same : (b, t) = (a, t) := f.plane.injective (by
    rw [plane_eq f b, plane_eq f a, eq])
  exact ab.ne' (congrArg Prod.fst same)

theorem fibreInv_left (f : CapHomeomorph) (y : ℝ) : Function.LeftInverse (fibreInv f y) (fibre f y) := by
  intro x
  change (f.plane.symm (fibre f y x, f.height y)).1 = x
  rw [← plane_eq, f.plane.symm_apply_apply]

theorem fibreInv_right (f : CapHomeomorph) (y : ℝ) : Function.RightInverse (fibreInv f y) (fibre f y) := by
  intro x
  have hy : (f.plane.symm (x, f.height y)).2 = y := by
    rw [symm_height, f.height.symm_apply_apply]
  change (f.plane (fibreInv f y x, y)).1 = x
  have eq : (fibreInv f y x, y) = f.plane.symm (x, f.height y) := Prod.ext rfl hy.symm
  rw [eq, f.plane.apply_symm_apply]

theorem fibreInv_strict (f : CapHomeomorph) (y : ℝ) : StrictMono (fibreInv f y) := by
  intro a b h
  apply (fibre_strict f y).lt_iff_lt.mp
  rw [fibreInv_right f y a, fibreInv_right f y b]
  exact h

/-- Conjugate horizontally by a global coordinate homeomorphism. -/
def conjugate (f : CapHomeomorph) (e : ℝ ≃ₜ ℝ) : CapHomeomorph where
  plane :=
    let lift := e.prodCongr (Homeomorph.refl ℝ)
    (lift.symm.trans f.plane).trans lift
  height := f.height
  increasing := f.increasing
  height_eq z := f.height_eq (e.symm z.1, z.2)
  outside z h := by
    change (e (f.plane (e.symm z.1, z.2)).1, (f.plane (e.symm z.1, z.2)).2) = z
    rw [f.outside (e.symm z.1, z.2) h, e.apply_symm_apply]

theorem conjugate_fibre (f : CapHomeomorph) (e : ℝ ≃ₜ ℝ) (x y : ℝ) :
    fibre (conjugate f e) y x = e (fibre f y (e.symm x)) := rfl

/-- Two interior cuts and their images stay strictly inside the strip
for every horizontal fibre. -/
structure Window (f : CapHomeomorph) where
  wallLeft : ℝ
  cutLeft : ℝ
  cutRight : ℝ
  wallRight : ℝ
  left_inside : wallLeft < cutLeft
  cut_order : cutLeft < cutRight
  right_inside : cutRight < wallRight
  left_image : ∀ y, wallLeft < fibre f y cutLeft
  right_image : ∀ y, fibre f y cutRight < wallRight

namespace Window

variable {f : CapHomeomorph} (w : Window f)

def source : Fin 4 → ℝ := knots w.wallLeft w.cutLeft w.cutRight w.wallRight

def target (y : ℝ) : Fin 4 → ℝ :=
  knots w.wallLeft (fibre f y w.cutLeft) (fibre f y w.cutRight) w.wallRight

theorem source_strict : StrictMono w.source :=
  knots_strict w.left_inside w.cut_order w.right_inside

theorem target_strict (y : ℝ) : StrictMono (w.target y) :=
  knots_strict (w.left_image y) (fibre_strict f y w.cut_order) (w.right_image y)

theorem target_continuous (i : Fin 4) : Continuous fun y => w.target y i := by
  fin_cases i
  · exact continuous_const
  · exact (f.plane.continuous.comp (continuous_const.prodMk continuous_id)).fst
  · exact (f.plane.continuous.comp (continuous_const.prodMk continuous_id)).fst
  · exact continuous_const

/-- Inside the middle interval use the given fibre map. At the walls and
outside them use the height map alone. Both pasted maps are continuous
by the clamped formula for splice. -/
def localizedPlane : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (splice w.source (w.target z.2) (fibre f z.2) z.1, f.height z.2)
  invFun z :=
    let y := f.height.symm z.2
    (splice (w.target y) w.source (fibreInv f y) z.1, y)
  left_inv z := by
    dsimp
    rw [f.height.symm_apply_apply]
    exact Prod.ext
      (splice_inverse w.source_strict (w.target_strict z.2) (fibre_strict f z.2)
        rfl rfl (fibreInv_left f z.2) z.1) rfl
  right_inv z := by
    dsimp
    rw [f.height.apply_symm_apply]
    let y := f.height.symm z.2
    exact Prod.ext
      (splice_inverse (w.target_strict y) w.source_strict (fibreInv_strict f y)
        (fibreInv_left f y w.cutLeft) (fibreInv_left f y w.cutRight)
        (fibreInv_right f y) z.1) rfl
  continuous_toFun :=
    (splice_continuous (fun _ => w.source_strict) (fun _ => continuous_const)
      w.target_continuous f.plane.continuous.fst).prodMk (f.height.continuous.comp continuous_snd)
  continuous_invFun := by
    let y := f.height.symm
    have invCont : Continuous fun z : ℝ × ℝ => fibreInv f (y z.2) z.1 :=
      (f.plane.symm.continuous.comp (continuous_fst.prodMk
        (f.height.continuous.comp (y.continuous.comp continuous_snd)))).fst
    exact (splice_continuous (a := fun t => w.target (y t)) (b := fun _ => w.source)
      (fun t => w.target_strict (y t))
      (fun i => (w.target_continuous i).comp y.continuous)
      (fun _ => continuous_const) invCont).prodMk (y.continuous.comp continuous_snd)

theorem localized_middle {x y : ℝ} (h : x ∈ Set.Icc w.cutLeft w.cutRight) :
    w.localizedPlane (x, y) = f.plane (x, y) := by
  rw [plane_eq]
  exact Prod.ext (splice_middle (a := w.source) (b := w.target y) h) rfl

theorem localized_exterior (z : ℝ × ℝ) (h : z.1 ≤ w.wallLeft ∨ w.wallRight ≤ z.1) :
    w.localizedPlane z = (z.1, f.height z.2) := by
  apply Prod.ext
  · change splice w.source (w.target z.2) (fibre f z.2) z.1 = z.1
    rcases h with low | high
    · rw [splice_low w.source_strict rfl (low.trans w.left_inside.le),
        transfer_left w.source_strict low]
      change w.wallLeft + (z.1 - w.wallLeft) = z.1
      exact add_sub_cancel _ _
    · rw [splice_high w.source_strict rfl (w.right_inside.le.trans high),
        transfer_right w.source_strict high]
      change w.wallRight + (z.1 - w.wallRight) = z.1
      exact add_sub_cancel _ _
  · rfl

theorem localized_fixed (z : ℝ × ℝ) (h : z.2 ≤ 0 ∨ 1 ≤ z.2) : w.localizedPlane z = z := by
  have eq : fibre f z.2 = id := funext (fibre_fixed f h)
  have same : w.target z.2 = w.source := by
    change knots w.wallLeft (fibre f z.2 w.cutLeft) (fibre f z.2 w.cutRight) w.wallRight = _
    rw [eq]
    rfl
  have hx : splice w.source (w.target z.2) (fibre f z.2) z.1 = z.1 := by
    rw [same, eq, splice_self w.source_strict]
  exact Prod.ext hx (height_fixed f h)

def localize : CapHomeomorph where
  plane := w.localizedPlane
  height := f.height
  increasing := f.increasing
  height_eq _ := rfl
  outside := w.localized_fixed

end Window
end Silmaril.RuntimeWires.Proofs.HorizontalComparison
