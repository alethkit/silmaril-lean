module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Height
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CapClasses

open ProgressiveGraph
open SlabIsotopy (place)
open CollarAssociator

def identity : CapHomeomorph where
  plane := Homeomorph.refl _
  height := Homeomorph.refl _
  increasing := strictMono_id
  height_eq _ := rfl
  outside _ _ := rfl

theorem strict_inverse (e : ℝ ≃ₜ ℝ) (h : StrictMono e) : StrictMono e.symm := by
  intro a b hab
  apply h.lt_iff_lt.mp
  simpa only [Homeomorph.apply_symm_apply] using hab

def symm (f : CapHomeomorph) : CapHomeomorph where
  plane := f.plane.symm
  height := f.height.symm
  increasing := strict_inverse f.height f.increasing
  height_eq z := by
    apply f.height.injective
    rw [Homeomorph.apply_symm_apply, ← f.height_eq, Homeomorph.apply_symm_apply]
  outside z h := f.plane.symm_apply_eq.mpr (f.outside z h).symm

def trans (f g : CapHomeomorph) : CapHomeomorph where
  plane := f.plane.trans g.plane
  height := f.height.trans g.height
  increasing := g.increasing.comp f.increasing
  height_eq z := by
    change (g.plane (f.plane z)).2 = g.height (f.height z.2)
    rw [g.height_eq, f.height_eq]
  outside z h := by
    change g.plane (f.plane z) = z
    rw [f.outside z h, g.outside z h]

noncomputable def halfAxis (offset : ℝ) : ℝ ≃ₜ ℝ where
  toFun := halfHeight offset
  invFun := slabHeight offset
  left_inv y := by unfold halfHeight slabHeight; ring
  right_inv y := by unfold halfHeight slabHeight; ring
  continuous_toFun := (continuous_id.add continuous_const).div_const 2
  continuous_invFun := (continuous_id.const_mul 2).sub continuous_const

theorem half_strict (offset : ℝ) : StrictMono (halfAxis offset) :=
  halfHeight_strictMono offset

noncomputable def placed (offset : ℝ) (f : CapHomeomorph) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (place offset).symm.trans (f.plane.trans (place offset))

noncomputable def placedHeight (offset : ℝ) (f : CapHomeomorph) : ℝ ≃ₜ ℝ :=
  (halfAxis offset).symm.trans (f.height.trans (halfAxis offset))

theorem placed_height_eq (offset : ℝ) (f : CapHomeomorph) (z : ℝ × ℝ) :
    (placed offset f z).2 = placedHeight offset f z.2 := by
  change halfHeight offset (f.plane (z.1, slabHeight offset z.2)).2 = _
  rw [f.height_eq]
  rfl

theorem placed_strict (offset : ℝ) (f : CapHomeomorph) : StrictMono (placedHeight offset f) :=
  (half_strict offset).comp (f.increasing.comp (strict_inverse (halfAxis offset) (half_strict offset)))

theorem placed_fixed (offset : ℝ) (f : CapHomeomorph) (z : ℝ × ℝ)
    (h : z.2 ≤ halfHeight offset 0 ∨ halfHeight offset 1 ≤ z.2) :
    placed offset f z = z := by
  have out : slabHeight offset z.2 ≤ 0 ∨ 1 ≤ slabHeight offset z.2 := by
    rcases h with h | h
    · left; unfold halfHeight slabHeight at *; linarith
    · right; unfold halfHeight slabHeight at *; linarith
  change place offset (f.plane ((place offset).symm z)) = _
  rw [f.outside _ out, Homeomorph.apply_symm_apply]

noncomputable def paste (f g : CapHomeomorph) : CapHomeomorph where
  plane := (placed 0 f).trans (placed 1 g)
  height := (placedHeight 0 f).trans (placedHeight 1 g)
  increasing := (placed_strict 1 g).comp (placed_strict 0 f)
  height_eq z := by
    change (placed 1 g (placed 0 f z)).2 = placedHeight 1 g (placedHeight 0 f z.2)
    rw [placed_height_eq, placed_height_eq]
  outside z h := by
    have lo : z.2 ≤ halfHeight 0 0 ∨ halfHeight 0 1 ≤ z.2 := by
      unfold halfHeight
      rcases h with h | h
      · exact .inl (by linarith)
      · exact .inr (by linarith)
    have hi : z.2 ≤ halfHeight 1 0 ∨ halfHeight 1 1 ≤ z.2 := by
      unfold halfHeight
      rcases h with h | h
      · exact .inl (by linarith)
      · exact .inr (by linarith)
    change placed 1 g (placed 0 f z) = z
    rw [placed_fixed 0 f z lo, placed_fixed 1 g z hi]

theorem paste_lower (f g : CapHomeomorph) (z : ℝ × ℝ) (h : z.2 ≤ 1 / 2) :
    (paste f g).plane z = placed 0 f z := by
  have atMid : placedHeight 0 f (1 / 2) = 1 / 2 := by
    rw [← placed_height_eq 0 f ((0 : ℝ), (1 / 2 : ℝ))]
    exact congrArg Prod.snd (placed_fixed 0 f ((0 : ℝ), (1 / 2 : ℝ))
      (.inr (by norm_num [halfHeight])))
  have below : (placed 0 f z).2 ≤ halfHeight 1 0 := by
    rw [placed_height_eq, show halfHeight 1 0 = 1 / 2 by norm_num [halfHeight], ← atMid]
    exact (placed_strict 0 f).monotone h
  exact placed_fixed 1 g _ (.inl below)

theorem paste_upper (f g : CapHomeomorph) (z : ℝ × ℝ) (h : 1 / 2 ≤ z.2) :
    (paste f g).plane z = placed 1 g z := by
  change placed 1 g (placed 0 f z) = _
  rw [placed_fixed 0 f z (.inr (by simpa [halfHeight] using h))]

theorem paste_place_lower (f g : CapHomeomorph) (z : ℝ × ℝ) (h : z.2 ≤ 1) :
    (paste f g).plane (place 0 z) = place 0 (f.plane z) := by
  rw [paste_lower f g _ (by change halfHeight 0 z.2 ≤ _; unfold halfHeight; linarith)]
  change place 0 (f.plane ((place 0).symm (place 0 z))) = _
  rw [Homeomorph.symm_apply_apply]

theorem paste_place_upper (f g : CapHomeomorph) (z : ℝ × ℝ) (h : 0 ≤ z.2) :
    (paste f g).plane (place 1 z) = place 1 (g.plane z) := by
  rw [paste_upper f g _ (by change _ ≤ halfHeight 1 z.2; unfold halfHeight; linarith)]
  change place 1 (g.plane ((place 1).symm (place 1 z))) = _
  rw [Homeomorph.symm_apply_apply]

noncomputable def collared (f g : CapHomeomorph) : CapHomeomorph := paste (paste f identity) g

theorem collared_lower (f g : CapHomeomorph) (z : ℝ × ℝ) (h : z.2 ≤ 1) :
    (collared f g).plane (z.1, Height.lower z.2) = ((f.plane z).1, Height.lower (f.plane z).2) := by
  change (paste (paste f identity) g).plane (place 0 (place 0 z)) = place 0 (place 0 (f.plane z))
  rw [paste_place_lower _ _ _ (by change halfHeight 0 z.2 ≤ _; unfold halfHeight; linarith),
    paste_place_lower _ _ _ h]

theorem collared_middle (f g : CapHomeomorph) (z : ℝ × ℝ) (h : z.2 ∈ Set.Icc (0 : ℝ) 1) :
    (collared f g).plane (z.1, Height.collar z.2) = (z.1, Height.collar z.2) := by
  change (paste (paste f identity) g).plane (place 0 (place 1 z)) = place 0 (place 1 z)
  rw [paste_place_lower _ _ _ (by change halfHeight 1 z.2 ≤ _; unfold halfHeight; linarith [h.2]),
    paste_place_upper _ _ _ h.1]
  rfl

theorem collared_upper (f g : CapHomeomorph) (z : ℝ × ℝ) (h : 0 ≤ z.2) :
    (collared f g).plane (z.1, Height.upper z.2) = ((g.plane z).1, Height.upper (g.plane z).2) :=
  paste_place_upper _ _ _ h

end Silmaril.RuntimeWires.Proofs.CapClasses
