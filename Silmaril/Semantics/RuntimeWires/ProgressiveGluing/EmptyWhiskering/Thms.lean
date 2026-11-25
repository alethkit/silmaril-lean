module

public import Mathlib.CategoryTheory.NatIso
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Comparison

public noncomputable section

/-!
# Naturality for whiskering beside an empty cap

In the two composites, the active drawing initially occupies different
height slabs. The geometric unit comparisons insert the lower and
upper straight pads that place the two active copies in the same middle
slab. A height-preserving ambient comparison of these padded drawings
matches every point of each of the five pieces. It sends the active
drawing by the appropriate affine half-strip placement and follows the
interpolating cap strands in the two outer slabs. The full comparison
composes with the geometric unit comparisons to recover the actual
two-operand composites.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip

open CategoryTheory
open Proofs.CapClasses (compare_trans compare_id compare_symm)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} (side : ActiveStrip)
variable {a b : FixedCap S}

/-- Fixed-outer-cap comparison of the two actual drawings in the empty
whiskering naturality square. -/
def compareEmptyWhisker (p : FixedDrawing S a.profile b.profile) :
    (p.thenDo (FixedCap.interpolationDrawing (side.empty_types b))).drawing.CapComparison
      ((FixedCap.interpolationDrawing (side.empty_types a)).thenDo
        (side.placeDrawing (a := a) (b := b) p (FixedCap.empty S))).drawing :=
  let q := FixedCap.interpolationDrawing (side.empty_types b)
  let r := FixedCap.interpolationDrawing (side.empty_types a)
  let placed := side.placeDrawing (a := a) (b := b) p (FixedCap.empty S)
  compare_trans (FixedDrawing.thenDo_comparison (p.compareLeftUnit a.inside) (compare_id q.drawing))
    (compare_trans (Proofs.EmptyWhiskering.compare side p)
      (compare_symm ((r.thenDo placed).compareRightUnit (side.adjoin b (FixedCap.empty S)).inside)))

theorem compareEmptyWhisker_increasing (p : FixedDrawing S a.profile b.profile) (y : ℝ) :
    StrictMono (fun x => ((side.compareEmptyWhisker (a := a) (b := b) p).map.plane (x, y)).1) :=
  Proofs.HorizontalComparison.fibre_strict (side.compareEmptyWhisker (a := a) (b := b) p).map y

theorem emptyWhisker_naturality (f : a ⟶ b) :
    f ≫ (side.emptyRecoordinate b).hom =
      (side.emptyRecoordinate a).hom ≫ (side.whisker (FixedCap.empty S)).map f := by
  refine Quotient.inductionOn f fun p => ?_
  change FixedCap.ofDrawing p ≫ (side.emptyRecoordinate b).hom =
    (side.emptyRecoordinate a).hom ≫ (side.whisker (FixedCap.empty S)).map (FixedCap.ofDrawing p)
  rw [side.whisker_drawings]
  change FixedCap.ofDrawing p ≫ FixedCap.ofDrawing (FixedCap.interpolationDrawing (side.empty_types b)) =
    FixedCap.ofDrawing (FixedCap.interpolationDrawing (side.empty_types a)) ≫
      FixedCap.ofDrawing (side.placeDrawing (a := a) (b := b) p (FixedCap.empty S))
  rw [FixedCap.comp_drawings, FixedCap.comp_drawings]
  exact CapClass.sound ⟨side.compareEmptyWhisker (a := a) (b := b) p⟩

/-- The identity functor and placement beside an empty idle cap are
naturally isomorphic by the actual straight coordinate-change drawings. -/
def emptyWhiskerIso : 𝟭 (FixedCap S) ≅ side.whisker (FixedCap.empty S) :=
  NatIso.ofComponents (side.emptyRecoordinate) (fun f => side.emptyWhisker_naturality f)

theorem emptyWhiskerIso_hom_app (a : FixedCap S) :
    (side.emptyWhiskerIso (S := S)).hom.app a = (side.emptyRecoordinate a).hom := by rfl

theorem emptyWhiskerIso_inv_app (a : FixedCap S) :
    (side.emptyWhiskerIso (S := S)).inv.app a = (side.emptyRecoordinate a).inv := by rfl

end Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip
