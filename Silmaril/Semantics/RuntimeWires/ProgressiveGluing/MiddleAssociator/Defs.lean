module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

/-- First place the active drawing to the right of A, then to the left of C. -/
def middleWhiskerLeft (A C : FixedCap S) : FixedCap S ⥤ FixedCap S :=
  ActiveStrip.right.whisker A ⋙ ActiveStrip.left.whisker C

/-- First place the active drawing to the left of C, then to the right of A. -/
def middleWhiskerRight (A C : FixedCap S) : FixedCap S ⥤ FixedCap S :=
  ActiveStrip.left.whisker C ⋙ ActiveStrip.right.whisker A

abbrev middleLeftCap (A B C : FixedCap S) :=
  ActiveStrip.left.adjoin (ActiveStrip.right.adjoin B A) C

abbrev middleRightCap (A B C : FixedCap S) :=
  ActiveStrip.right.adjoin (ActiveStrip.left.adjoin B C) A

variable {B D : FixedCap S}

/-- Representative of the left-parenthesized double whiskering. -/
def middleLeftDrawing (A C : FixedCap S) (p : FixedDrawing S B.profile D.profile) :
    FixedDrawing S (middleLeftCap A B C).profile (middleLeftCap A D C).profile := by
  exact ActiveStrip.left.placeDrawing (a := ActiveStrip.right.adjoin B A) (b := ActiveStrip.right.adjoin D A)
    (ActiveStrip.right.placeDrawing (a := B) (b := D) p A) C

/-- Representative of the right-parenthesized double whiskering. -/
def middleRightDrawing (A C : FixedCap S) (p : FixedDrawing S B.profile D.profile) :
    FixedDrawing S (middleRightCap A B C).profile (middleRightCap A D C).profile := by
  exact ActiveStrip.right.placeDrawing (a := ActiveStrip.left.adjoin B C) (b := ActiveStrip.left.adjoin D C)
    (ActiveStrip.left.placeDrawing (a := B) (b := D) p C) A

theorem middleAssociator_types (A B C : FixedCap S) :
    (middleLeftCap A B C).types = (middleRightCap A B C).types := by
  simp only [middleLeftCap, middleRightCap, FixedCap.types, ActiveStrip.adjoin_labels, List.append_assoc]

/-- The horizontal associator component interpolates the ordered slots
between the two actual fixed cap profiles. -/
def middleAssociatorComponent (A B C : FixedCap S) :
    (middleWhiskerLeft A C).obj B ≅ (middleWhiskerRight A C).obj B :=
  FixedCap.recoordinateIso (by exact middleAssociator_types A B C)

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap
