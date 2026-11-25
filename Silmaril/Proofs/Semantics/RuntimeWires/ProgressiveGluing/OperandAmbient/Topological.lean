module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.OperandAmbient

open ProgressiveGraph SlabIsotopy

theorem placed_height (f : SlabIsotopy) (offset : ℝ) (t : Time) (z : ℝ × ℝ) :
    (f.placed offset t z).2 = z.2 := by
  change halfHeight offset ((f.frame t) (z.1, slabHeight offset z.2)).2 = _
  rw [f.height]
  unfold halfHeight slabHeight
  ring

theorem placed_outside (f : SlabIsotopy) (offset : ℝ) (t : Time) (z : ℝ × ℝ)
    (outside : z.2 ≤ halfHeight offset 0 ∨ halfHeight offset 1 ≤ z.2) :
    f.placed offset t z = z := by
  have h : slabHeight offset z.2 ≤ 0 ∨ 1 ≤ slabHeight offset z.2 := by
    rcases outside with low | high
    · left
      unfold slabHeight halfHeight at *
      linarith
    · right
      unfold slabHeight halfHeight at *
      linarith
  change (place offset) (f.frame t ((place offset).symm z)) = z
  rw [f.outside _ _ h, Homeomorph.apply_symm_apply]

theorem placed_zero (f : SlabIsotopy) (offset : ℝ) (z : ℝ × ℝ) :
    f.placed offset ⟨0, le_rfl, zero_le_one⟩ z = z := by
  change (place offset) (f.frame _ ((place offset).symm z)) = z
  rw [f.zero, Homeomorph.apply_symm_apply]

theorem placed_continuous (f : SlabIsotopy) (offset : ℝ) :
    Continuous (fun z : Time × (ℝ × ℝ) => f.placed offset z.1 z.2) :=
  (place offset).continuous.comp (f.continuous_frame.comp
    (continuous_fst.prodMk ((place offset).symm.continuous.comp continuous_snd)))

theorem placed_inverse_continuous (f : SlabIsotopy) (offset : ℝ) :
    Continuous (fun z : Time × (ℝ × ℝ) => (f.placed offset z.1).symm z.2) :=
  (place offset).continuous.comp (f.continuous_inverse.comp
    (continuous_fst.prodMk ((place offset).symm.continuous.comp continuous_snd)))

/-- Compose the two placed maps. Their open supports are disjoint. -/
noncomputable def paste (f g : SlabIsotopy) : SlabIsotopy where
  frame t := (f.placed 0 t).trans (g.placed 1 t)
  zero z := by
    change g.placed 1 _ (f.placed 0 _ z) = _
    rw [placed_zero, placed_zero]
  continuous_frame := (placed_continuous g 1).comp (continuous_fst.prodMk (placed_continuous f 0))
  continuous_inverse := (placed_inverse_continuous f 0).comp
    (continuous_fst.prodMk (placed_inverse_continuous g 1))
  height t z := (placed_height g 1 t _).trans (placed_height f 0 t z)
  outside t z outside := by
    have lower : z.2 ≤ halfHeight 0 0 ∨ halfHeight 0 1 ≤ z.2 := by
      rcases outside with low | high
      · exact .inl (by simpa [halfHeight] using low)
      · exact .inr (by unfold halfHeight; linarith)
    have upper : z.2 ≤ halfHeight 1 0 ∨ halfHeight 1 1 ≤ z.2 := by
      rcases outside with low | high
      · exact .inl (by unfold halfHeight; linarith)
      · exact .inr (by simpa [halfHeight] using high)
    change g.placed 1 t (f.placed 0 t z) = z
    rw [placed_outside f 0 t z lower, placed_outside g 1 t z upper]

theorem paste_lower (f g : SlabIsotopy) (t : Time) (z : ℝ × ℝ) (hy : z.2 ≤ 1 / 2) :
    (paste f g).frame t z = f.placed 0 t z := by
  change g.placed 1 t (f.placed 0 t z) = _
  apply placed_outside
  left
  simpa only [placed_height, show halfHeight 1 0 = 1 / 2 by norm_num [halfHeight]] using hy

theorem paste_upper (f g : SlabIsotopy) (t : Time) (z : ℝ × ℝ) (hy : 1 / 2 ≤ z.2) :
    (paste f g).frame t z = g.placed 1 t z := by
  change g.placed 1 t (f.placed 0 t z) = _
  rw [placed_outside f 0 t z (.inr (by simpa [halfHeight] using hy))]

def stationary : SlabIsotopy where
  frame _ := Homeomorph.refl _
  zero _ := rfl
  continuous_frame := continuous_snd
  continuous_inverse := continuous_snd
  height _ _ := rfl
  outside _ _ _ := rfl

end Silmaril.RuntimeWires.Proofs.OperandAmbient
