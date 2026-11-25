module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Thms

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O}
variable (side : ActiveStrip) (near far : FixedCap S)

/-- Place an outer active drawing by adjoining its nearer idle profile
first and then the farther one. -/
def nestedWhisker : FixedCap S ⥤ FixedCap S :=
  side.whisker near ⋙ side.whisker far

/-- Place the same active drawing beside the already combined idle profiles. -/
def groupedWhisker : FixedCap S ⥤ FixedCap S :=
  side.whisker (side.adjoin near far)

abbrev nestedCap (a : FixedCap S) := side.adjoin (side.adjoin a near) far
abbrev groupedCap (a : FixedCap S) := side.adjoin a (side.adjoin near far)

/-- Left parenthesization, with the active drawing in the selected outer slot. -/
def outerAssociatorSource : FixedCap S ⥤ FixedCap S :=
  match side with
  | .left => side.nestedWhisker near far
  | .right => side.groupedWhisker near far

/-- Right parenthesization, with the active drawing in the selected outer slot. -/
def outerAssociatorTarget : FixedCap S ⥤ FixedCap S :=
  match side with
  | .left => side.groupedWhisker near far
  | .right => side.nestedWhisker near far

abbrev outerSourceCap (a : FixedCap S) := (side.outerAssociatorSource near far).obj a
abbrev outerTargetCap (a : FixedCap S) := (side.outerAssociatorTarget near far).obj a

theorem nested_grouped_types (a : FixedCap S) :
    (side.nestedCap near far a).types = (side.groupedCap near far a).types := by
  cases side <;> simp only [nestedCap, groupedCap, FixedCap.types, adjoin_labels, List.append_assoc]

theorem outerAssociator_types (a : FixedCap S) :
    (side.outerSourceCap near far a).types = (side.outerTargetCap near far a).types := by
  cases side
  · exact ActiveStrip.left.nested_grouped_types near far a
  · exact (ActiveStrip.right.nested_grouped_types near far a).symm

/-- The component interpolates the actual ordered cap contacts from the
left to the right parenthesization. -/
def outerAssociatorComponent (a : FixedCap S) :
    side.outerSourceCap near far a ≅ side.outerTargetCap near far a :=
  FixedCap.recoordinateIso (side.outerAssociator_types near far a)

variable {a b : FixedCap S}

def nestedDrawing (p : FixedDrawing S a.profile b.profile) :
    FixedDrawing S (side.nestedCap near far a).profile (side.nestedCap near far b).profile :=
  side.placeDrawing (a := side.adjoin a near) (b := side.adjoin b near)
    (side.placeDrawing (a := a) (b := b) p near) far

def groupedDrawing (p : FixedDrawing S a.profile b.profile) :
    FixedDrawing S (side.groupedCap near far a).profile (side.groupedCap near far b).profile :=
  side.placeDrawing (a := a) (b := b) p (side.adjoin near far)

def outerSourceDrawing (p : FixedDrawing S a.profile b.profile) :
    FixedDrawing S (side.outerSourceCap near far a).profile (side.outerSourceCap near far b).profile := by
  cases side
  · exact ActiveStrip.left.nestedDrawing (a := a) (b := b) near far p
  · exact ActiveStrip.right.groupedDrawing (a := a) (b := b) near far p

def outerTargetDrawing (p : FixedDrawing S a.profile b.profile) :
    FixedDrawing S (side.outerTargetCap near far a).profile (side.outerTargetCap near far b).profile := by
  cases side
  · exact ActiveStrip.left.groupedDrawing (a := a) (b := b) near far p
  · exact ActiveStrip.right.nestedDrawing (a := a) (b := b) near far p

end Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip
