module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarAmbient
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarMotion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CollarCombined

open ProgressiveGraph
open SlabIsotopy (Time place)
open Proofs.ProgressiveGluing (polygonalDrawing)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {W : ℕ} {cap : CollarSpec O W}

/-- Placement of the collar in the composite, y ↦ (y + 1) / 4. -/
noncomputable def collarPlace : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (place 1).trans (place 0)

theorem place_fst (z : ℝ × ℝ) : (collarPlace z).1 = z.1 := rfl

theorem place_snd (z : ℝ × ℝ) : (collarPlace z).2 = (z.2 + 1) / 4 := by
  change halfHeight 0 (halfHeight 1 z.2) = _
  unfold halfHeight
  ring

theorem unplace_fst (z : ℝ × ℝ) : (collarPlace.symm z).1 = z.1 := rfl

theorem unplace_snd (z : ℝ × ℝ) : (collarPlace.symm z).2 = 4 * z.2 - 1 := by
  change slabHeight 1 (slabHeight 0 z.2) = _
  unfold slabHeight
  ring

variable (p q : PolygonalCollar cap)

/-- Pull the existing collar isotopy back to unit height. This is the
isotopy supplied to the generic partial gluing theorem. -/
noncomputable def normalized : SlabIsotopy where
  frame t := collarPlace.trans ((p.ambientIsotopy q t).trans collarPlace.symm)
  zero z := by
    change collarPlace.symm (p.ambientIsotopy q _ (collarPlace z)) = z
    rw [p.ambientIsotopy_zero, Homeomorph.symm_apply_apply]
  continuous_frame := collarPlace.symm.continuous.comp (p.ambientIsotopy_continuous q |>.comp
    (continuous_fst.prodMk (collarPlace.continuous.comp continuous_snd)))
  continuous_inverse := collarPlace.symm.continuous.comp (p.ambientIsotopy_symm_continuous q |>.comp
    (continuous_fst.prodMk (collarPlace.continuous.comp continuous_snd)))
  height t z := by
    change (collarPlace.symm (p.ambientIsotopy q t (collarPlace z))).2 = z.2
    rw [unplace_snd, p.ambientIsotopy_height, place_snd]
    ring
  outside t z outside := by
    have out : (collarPlace z).2 ≤ 1 / 4 ∨ 1 / 2 ≤ (collarPlace z).2 := by
      rw [place_snd]
      rcases outside with low | high
      · exact .inl (by linarith)
      · exact .inr (by linarith)
    change collarPlace.symm (p.ambientIsotopy q t (collarPlace z)) = z
    rw [p.ambientIsotopy_outside q t _ out, Homeomorph.symm_apply_apply]

theorem normalized_wire (t : Time) (w : Fin W) (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (normalized p q).frame t ((p.wire w).x y, y) = (((p.blend q t).wire w).x y, y) := by
  let z := collarPlace ((p.wire w).x y, y)
  have hz : z.2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) := by
    change (collarPlace ((p.wire w).x y, y)).2 ∈ _
    rw [place_snd]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have scale : 4 * z.2 - 1 = y := by
    change 4 * (collarPlace ((p.wire w).x y, y)).2 - 1 = y
    rw [place_snd]
    ring
  have h := p.ambientIsotopy_wire q t w hz
  rw [scale] at h
  have eq : ((p.wire w).x y, z.2) = z := Prod.ext (place_fst _).symm rfl
  change collarPlace.symm (p.ambientIsotopy q t z) = _
  rw [← eq, h]
  exact Prod.ext (unplace_fst _) ((unplace_snd _).trans scale)

noncomputable def collarMotion : (polygonalDrawing (S := S) p).AmbientMotion where
  isotopy := normalized p q
  wireCount _ := W
  drawing t := polygonalDrawing (p.blend q t)
  correspondence t :=
    { rename := Equiv.refl _
      heights := rfl
      generators := rfl
      label _ := rfl
      start _ := rfl
      finish _ := rfl
      inputs j := j.elim0
      outputs j := j.elim0
      wire w y hy := normalized_wire p q t w y hy
      vertex j := j.elim0 }

end Silmaril.RuntimeWires.Proofs.CollarCombined
