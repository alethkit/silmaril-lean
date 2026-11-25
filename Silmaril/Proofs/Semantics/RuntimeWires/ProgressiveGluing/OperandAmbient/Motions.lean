module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Frames
import Mathlib.Tactic.Linarith

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.OperandAmbient

open ProgressiveGraph ProgressiveGraph.Diagram
open SlabIsotopy (Time place)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V A B : ℕ}
variable {d : ProgressiveGraph.Diagram S V A .point} {e : ProgressiveGraph.Diagram S V B .point}
variable {f : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)}

theorem frameTrace (p : d.AmbientFrame e f) (w : Fin A) :
    f '' (d.wire w).trace = (e.wire (p.rename w)).trace := by
  change f '' ((d.wire w).point '' Set.Icc (d.lower w) (d.upper w)) =
    (e.wire (p.rename w)).point '' Set.Icc (e.lower (p.rename w)) (e.upper (p.rename w))
  rw [lower_eq p, upper_eq p, Set.image_image]
  exact Set.image_congr (fun y hy => p.wire w y hy)

def stationaryMotion (d : ProgressiveGraph.Diagram S V A .point) : d.AmbientMotion where
  isotopy := stationary
  wireCount _ := A
  drawing _ := d
  correspondence _ :=
    { rename := Equiv.refl _
      heights := rfl
      generators := rfl
      label _ := rfl
      start _ := rfl
      finish _ := rfl
      inputs _ := by simp
      outputs _ := by simp
      wire _ _ _ := rfl
      vertex _ := rfl }

variable {R C : ℕ} {b : ProgressiveGraph.Diagram S R C .point}

noncomputable def gluedMotion (m : d.PartialVerticalMatch b)
    (p : d.AmbientMotion) (q : b.AmbientMotion) : m.glue.AmbientMotion where
  isotopy := paste p.isotopy q.isotopy
  wireCount t := PartialVerticalMatch.wireCount (p.drawing t) (q.drawing t)
  drawing t := (movedMatch p.isotopy q.isotopy t (p.correspondence t) (q.correspondence t) m).glue
  correspondence t := gluedFrame p.isotopy q.isotopy t (p.correspondence t) (q.correspondence t) m

private theorem stationary_placed (t : Time) (offset : ℝ) (z : ℝ × ℝ) :
    stationary.placed offset t z = z := (place offset).apply_symm_apply z

variable (p q : SlabIsotopy) (t : Time) (z : ℝ × ℝ)

theorem collared_lower (hy : z.2 ≤ 1 / 4) :
    (paste (paste p stationary) q).frame t z =
      place 0 (place 0 (p.frame t ((place 0).symm ((place 0).symm z)))) := by
  rw [paste_lower _ _ _ _ (by linarith)]
  change place 0 ((paste p stationary).frame t ((place 0).symm z)) = _
  rw [paste_lower _ _ _ _ (by change slabHeight 0 z.2 ≤ _; unfold slabHeight; linarith)]
  rfl

theorem collared_upper (hy : 1 / 2 ≤ z.2) :
    (paste (paste p stationary) q).frame t z = place 1 (q.frame t ((place 1).symm z)) :=
  paste_upper _ _ _ _ hy

theorem collared_fixed (hy : z.2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (paste (paste p stationary) q).frame t z = z := by
  rw [paste_lower _ _ _ _ hy.2]
  change place 0 ((paste p stationary).frame t ((place 0).symm z)) = z
  rw [paste_upper _ _ _ _ (by change _ ≤ slabHeight 0 z.2; unfold slabHeight; linarith [hy.1]),
    stationary_placed, Homeomorph.apply_symm_apply]

end Silmaril.RuntimeWires.Proofs.OperandAmbient
