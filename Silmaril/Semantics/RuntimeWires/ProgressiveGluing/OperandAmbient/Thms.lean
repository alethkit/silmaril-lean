module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Motions

public section

/-!
# Ambient gluing with fixed cap cuts

The construction concerns vertical juxtaposition in Figure 7 and Lemma
3.4 of Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal
Categories*, arXiv:2305.06075v5, pp. 9:6–9:7. It works with fixed cap
contacts and with height-preserving ambient isotopies supported in the
operand slabs. The pinned PDF SHA-256 is
`8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

namespace SlabIsotopy

/-- Paste by composing the conjugated maps, which have disjoint open supports.
Both joint continuity laws are part of the resulting isotopy. -/
noncomputable def paste (f g : SlabIsotopy) : SlabIsotopy := Proofs.OperandAmbient.paste f g

theorem paste_lower (f g : SlabIsotopy) (t : Time) (z : ℝ × ℝ) (hy : z.2 ≤ 1 / 2) :
    (f.paste g).frame t z = f.placed 0 t z := Proofs.OperandAmbient.paste_lower f g t z hy

theorem paste_upper (f g : SlabIsotopy) (t : Time) (z : ℝ × ℝ) (hy : 1 / 2 ≤ z.2) :
    (f.paste g).frame t z = g.placed 1 t z := Proofs.OperandAmbient.paste_upper f g t z hy

end SlabIsotopy

namespace Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B C : ℕ}
variable {d : Diagram S L A .point} {b : Diagram S R B .point}

namespace AmbientFrame

variable {e : Diagram S L C .point} {f : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)}

def bottomContact (p : d.AmbientFrame e f) : {w // d.start w = none} ≃ {w // e.start w = none} :=
  Proofs.OperandAmbient.bottom p

def topContact (p : d.AmbientFrame e f) : PartialVerticalMatch.Contact d ≃ PartialVerticalMatch.Contact e :=
  Proofs.OperandAmbient.top p

/-- Each whole trace is carried to the trace with its renamed wire ID. -/
theorem trace (p : d.AmbientFrame e f) (w : Fin A) :
    f '' (d.wire w).trace = (e.wire (p.rename w)).trace :=
  Proofs.OperandAmbient.frameTrace p w

end AmbientFrame

def AmbientMotion.stationary (d : Diagram S L A .point) : d.AmbientMotion :=
  Proofs.OperandAmbient.stationaryMotion d

namespace PartialVerticalMatch

variable (m : d.PartialVerticalMatch b) (p : d.AmbientMotion) (q : b.AmbientMotion)

/-- Transport the original typed matching by the corresponding cap IDs. -/
def motionMatch (t : SlabIsotopy.Time) : (p.drawing t).PartialVerticalMatch (q.drawing t) :=
  Proofs.OperandAmbient.movedMatch p.isotopy q.isotopy t (p.correspondence t) (q.correspondence t) m

theorem motionMatch_contact (t : SlabIsotopy.Time) (w : Contact d) :
    (m.motionMatch p q t).contact ((p.correspondence t).topContact w) =
      (q.correspondence t).bottomContact (m.contact w) :=
  Proofs.OperandAmbient.contact_renamed _ _ m
    (fun x => p.isotopy.outside t (x, 1) (.inr le_rfl))
    (fun x => q.isotopy.outside t (x, 0) (.inl le_rfl)) w

/-- Glue the actual operand frames at each time. The correspondence preserves
vertex heights, incidence, labels, and ordered ports under the same renaming. -/
noncomputable def glueMotion : m.glue.AmbientMotion :=
  Proofs.OperandAmbient.gluedMotion m p q

theorem glueMotion_wireCount (t : SlabIsotopy.Time) :
    (m.glueMotion p q).wireCount t = wireCount (p.drawing t) (q.drawing t) := by rfl

theorem glueMotion_drawing (t : SlabIsotopy.Time) :
    HEq ((m.glueMotion p q).drawing t) (m.motionMatch p q t).glue := by rfl

theorem glueMotion_isotopy : (m.glueMotion p q).isotopy = p.isotopy.paste q.isotopy := by rfl

end PartialVerticalMatch

namespace OrderedVerticalMatch

variable (m : d.OrderedVerticalMatch b) (p : d.AmbientMotion) (q : b.AmbientMotion)

/-- Lift supported ambient operand isotopies through the two actual joins
of the ordered cap gluing. The affine collar is kept fixed. -/
noncomputable def glueOperands : m.glue.AmbientMotion :=
  let n := m.upperJoin.glueMotion (m.lowerJoin.glueMotion p (.stationary m.collar)) q
  { isotopy := n.isotopy
    wireCount := n.wireCount
    drawing := n.drawing
    correspondence t := by rw [m.glue_eq_upperJoin]; exact n.correspondence t }

theorem glueOperands_lower (t : SlabIsotopy.Time) (z : ℝ × ℝ) (hy : z.2 ≤ 1 / 4) :
    (m.glueOperands p q).isotopy.frame t z =
      SlabIsotopy.place 0 (SlabIsotopy.place 0
        (p.isotopy.frame t ((SlabIsotopy.place 0).symm ((SlabIsotopy.place 0).symm z)))) :=
  Proofs.OperandAmbient.collared_lower p.isotopy q.isotopy t z hy

theorem glueOperands_upper (t : SlabIsotopy.Time) (z : ℝ × ℝ) (hy : 1 / 2 ≤ z.2) :
    (m.glueOperands p q).isotopy.frame t z =
      SlabIsotopy.place 1 (q.isotopy.frame t ((SlabIsotopy.place 1).symm z)) :=
  Proofs.OperandAmbient.collared_upper p.isotopy q.isotopy t z hy

/-- The full collar slab, including both splices, is fixed pointwise. -/
theorem glueOperands_collar (t : SlabIsotopy.Time) (z : ℝ × ℝ)
    (hy : z.2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (m.glueOperands p q).isotopy.frame t z = z :=
  Proofs.OperandAmbient.collared_fixed p.isotopy q.isotopy t z hy

end OrderedVerticalMatch
end Diagram
end Silmaril.RuntimeWires.ProgressiveGraph
