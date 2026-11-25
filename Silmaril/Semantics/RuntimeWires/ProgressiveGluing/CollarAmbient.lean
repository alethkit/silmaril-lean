module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarMotion
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarAmbientGlued

public section

/-!
# Ambient extension of fixed-cap collar motion

This gives a height-preserving ambient isotopy for the collar in the
vertical juxtaposition of Figure 7 and Lemma 3.4, using the progressive
graphs of Definition 3.2. See Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5, pp. 9:6–9:7.
The pinned PDF SHA-256 is
`8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v

namespace PolygonalCollar

variable {O : Type u} {W : ℕ} {cap : CollarSpec O W} (p q : PolygonalCollar cap)

/-- Ordered horizontal coordinates at a composite height, clamped to the
collar caps, with the fixed side coordinates 0 and 1. -/
noncomputable def horizontalKnots (y : ℝ) : Fin (W + 2) → ℝ :=
  Proofs.CollarAmbient.knots p (Proofs.CollarAmbient.height y)

theorem horizontalKnots_strict (y : ℝ) : StrictMono (p.horizontalKnots y) :=
  Proofs.CollarAmbient.knots_strict p _

/-- The time-dependent ambient homeomorphism of the plane. The collar is
placed between heights 1/4 and 1/2, as in ordered cap gluing. -/
noncomputable def ambientIsotopy (t : Time) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  Proofs.CollarAmbient.ambient p q t

/-- Every horizontal fiber uses the increasing affine interpolation
between consecutive knots. -/
theorem ambientIsotopy_x (t : Time) (x y : ℝ) :
    (p.ambientIsotopy q t (x, y)).1 =
      OrderedKnots.transfer (p.horizontalKnots y) ((p.blend q t).horizontalKnots y) x := by rfl

theorem ambientIsotopy_height (t : Time) (z : ℝ × ℝ) :
    (p.ambientIsotopy q t z).2 = z.2 := by rfl

theorem ambientIsotopy_increasing (t : Time) (y : ℝ) :
    StrictMono (fun x => (p.ambientIsotopy q t (x, y)).1) :=
  Proofs.CollarAmbient.ambient_increasing p q t y

theorem ambientIsotopy_zero (z : ℝ × ℝ) :
    p.ambientIsotopy q ⟨0, le_rfl, zero_le_one⟩ z = z :=
  Proofs.CollarAmbient.ambient_zero p q z

/-- The two splice caps and the entire complement of the open collar slab are fixed. -/
theorem ambientIsotopy_outside (t : Time) (z : ℝ × ℝ) (h : z.2 ≤ 1 / 4 ∨ 1 / 2 ≤ z.2) :
    p.ambientIsotopy q t z = z :=
  Proofs.CollarAmbient.ambient_outside p q t z h

theorem ambientIsotopy_outside_sides (t : Time) (z : ℝ × ℝ) (h : z.1 ≤ 0 ∨ 1 ≤ z.1) :
    p.ambientIsotopy q t z = z :=
  Proofs.CollarAmbient.ambient_outside_sides p q t z h

theorem ambientIsotopy_continuous :
    Continuous (fun z : Time × (ℝ × ℝ) => p.ambientIsotopy q z.1 z.2) :=
  Proofs.CollarAmbient.frame_continuous p q

theorem ambientIsotopy_symm_continuous :
    Continuous (fun z : Time × (ℝ × ℝ) => (p.ambientIsotopy q z.1).symm z.2) :=
  Proofs.CollarAmbient.inverse_continuous p q

theorem ambientIsotopy_wire (t : Time) (w : Fin W) {y : ℝ} (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    p.ambientIsotopy q t ((p.wire w).x (4 * y - 1), y) =
      (((p.blend q t).wire w).x (4 * y - 1), y) :=
  Proofs.CollarAmbient.ambient_wire p q t w hy

end PolygonalCollar

namespace Diagram.OrderedVerticalMatch

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper) (p q : PolygonalCollar m.collarSpec)

/-- Exact action on every covered point of every composite wire, with the
same wire ID and height. The wire intervals and labels are fixed. -/
theorem ambientIsotopy_glue_wire (t : PolygonalCollar.Time) (w : Fin m.gluedWireCount) {y : ℝ}
    (cover : (m.glueWith p).covers w y) :
    p.ambientIsotopy q t ((m.glueWith p).x w y, y) = ((m.glueWith (p.blend q t)).x w y, y) :=
  Proofs.CollarAmbient.ambient_glued_wire m p q t w cover

/-- The ambient homeomorphism sends the whole trace of each indexed
composite wire to its trace in the moving drawing. -/
theorem ambientIsotopy_glue_trace (t : PolygonalCollar.Time) (w : Fin m.gluedWireCount) :
    p.ambientIsotopy q t '' ((m.glueWith p).wire w).trace = ((m.glueWith (p.blend q t)).wire w).trace :=
  Proofs.CollarAmbient.ambient_glued_trace m p q t w

/-- Exact action on vertices of the composite. The vertices of both
operands are stationary. -/
theorem ambientIsotopy_glue_vertex (t : PolygonalCollar.Time) (j : Fin (L + R)) :
    p.ambientIsotopy q t ((m.glueWith p).vertexX j, (m.glueWith p).vertexHeight j) =
      ((m.glueWith (p.blend q t)).vertexX j, (m.glueWith (p.blend q t)).vertexHeight j) :=
  Proofs.CollarAmbient.ambient_glued_vertex m p q t j

end Diagram.OrderedVerticalMatch
end Silmaril.RuntimeWires.ProgressiveGraph
