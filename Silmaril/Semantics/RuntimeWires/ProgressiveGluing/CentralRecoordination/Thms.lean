module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CentralRecoordination.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CentralRecoordination.Comparison

public noncomputable section

/-!
# Centrality of fixed-cap recoordination

The arbitrary drawing stays in its own strip. The comparison aligns its
two height placements using the geometric units and slides the coordinate
change in the opposite strip through the resulting common slab. Ordered
knot interpolation in that strip fixes its walls and preserves the
corresponding idle wire IDs. The framed comparison preserves all full
traces and ordered incidence. Whiskered recoordination identifies the
straight interpolations used in the framing with the actual placed
drawings in the two composites.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory
universe u v
variable {O : Type u} {S : Signature.{u,v} O}

namespace ActiveStrip

variable (side : ActiveStrip) {a a' b d : FixedCap S} (h : a.types = a'.types)

/-- The two actual orders of collared composition have a fixed-outer-cap
comparison for either choice of the strip carrying the arbitrary drawing. -/
def compareRecoordinationSlide (p : FixedDrawing S b.profile d.profile) :
    ((side.placeDrawing (a := b) (b := d) p a).thenDo
      (side.oppositeRecoordination d h)).drawing.CapComparison
      ((side.oppositeRecoordination b h).thenDo
        (side.placeDrawing (a := b) (b := d) p a')).drawing :=
  Proofs.CentralRecoordination.compareSlide side h p

theorem recoordinate_slide (f : b ⟶ d) :
    (side.whisker a).map f ≫ FixedCap.ofDrawing (side.oppositeRecoordination d h) =
      FixedCap.ofDrawing (side.oppositeRecoordination b h) ≫ (side.whisker a').map f :=
  Proofs.CentralRecoordination.slide side h f

end ActiveStrip

namespace FixedCap

/-- Canonical recoordination satisfies both sequential tensor equations of
the repository's centrality predicate. -/
theorem recoordinate_central {a a' : FixedCap S} (h : a.types = a'.types) :
    @PremonoidalCategory.IsCentral (FixedCap S) inferInstance (geometricMonoidalData S)
      a a' (recoordinate h) :=
  Proofs.CentralRecoordination.central h

theorem objectAssociator_central (A B C : FixedCap S) :
    @PremonoidalCategory.IsCentral (FixedCap S) inferInstance (geometricMonoidalData S)
      _ _ (objectAssociator A B C).hom := by
  rw [objectAssociator_hom]
  exact recoordinate_central (objectAssociator_types A B C)

theorem leftUnitor_central (A : FixedCap S) :
    @PremonoidalCategory.IsCentral (FixedCap S) inferInstance (geometricMonoidalData S)
      _ _ (leftUnitor A).hom := by
  rw [leftUnitor_hom]
  exact recoordinate_central (leftUnitor_types A)

theorem rightUnitor_central (A : FixedCap S) :
    @PremonoidalCategory.IsCentral (FixedCap S) inferInstance (geometricMonoidalData S)
      _ _ (rightUnitor A).hom := by
  rw [rightUnitor_hom]
  exact recoordinate_central (rightUnitor_types A)

end FixedCap
end Silmaril.RuntimeWires.ProgressiveGraph
