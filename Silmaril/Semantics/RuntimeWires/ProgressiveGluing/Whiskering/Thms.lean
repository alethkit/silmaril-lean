module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching

public noncomputable section

/-!
# Whiskering by a fixed idle cap

The two vertical composites have the same geometric pieces after typed
wire renaming. The active operands and their actual affine collar use
the same height placements on both sides. Matching through the common
ordered cap slots leaves each active collar strand at its affinely
rescaled contact coordinate. The two idle copies and their collar form
one straight strand per idle slot.

This gives the left and right whiskering functors for the fixed-contact
category, toward Lemma 3.4 and Figure 7 of Román and Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.
The halves retain their existing coordinates.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c : FixedCap S}
variable (side : ActiveStrip) (idle : FixedCap S)

theorem composition_input_slot (p : FixedDrawing S a.profile b.profile)
    (q : FixedDrawing S b.profile c.profile) (i : Fin (side.adjoin a idle).profile.size) :
    (side.compareComposition idle p q).incidence.wire
        ((side.placeDrawing (a := a) (b := c) (p.thenDo q) idle).input i).val =
      (((side.placeDrawing p idle).thenDo (side.placeDrawing q idle)).input i).val :=
  congrArg Subtype.val (Proofs.CapClasses.input_slot (side.compareComposition idle p q) i)

theorem composition_output_slot (p : FixedDrawing S a.profile b.profile)
    (q : FixedDrawing S b.profile c.profile) (i : Fin (side.adjoin c idle).profile.size) :
    (side.compareComposition idle p q).incidence.wire
        ((side.placeDrawing (a := a) (b := c) (p.thenDo q) idle).output i).val =
      (((side.placeDrawing p idle).thenDo (side.placeDrawing q idle)).output i).val :=
  congrArg Subtype.val (Proofs.CapClasses.output_slot (side.compareComposition idle p q) i)

theorem placeClass_identity (a : FixedCap S) :
    side.placeClass (a := a) (b := a) idle (CapClass.identity S a.profile a.inside) =
      CapClass.identity S (side.adjoin a idle).profile (side.adjoin a idle).inside := by
  change side.placeClass (a := a) (b := a) idle
      (CapClass.ofDrawing (FixedDrawing.identity S a.profile a.inside)) = _
  rw [placeClass_drawings]
  exact CapClass.sound ⟨side.compareIdentity idle a⟩

theorem placeClass_comp (f : CapClass S a.profile b.profile) (g : CapClass S b.profile c.profile) :
    side.placeClass (a := a) (b := c) idle (f.thenDo g) =
      (side.placeClass (a := a) (b := b) idle f).thenDo (side.placeClass (a := b) (b := c) idle g) := by
  refine Quotient.inductionOn₂ f g fun p q => ?_
  change side.placeClass (a := a) (b := c) idle ((CapClass.ofDrawing p).thenDo (CapClass.ofDrawing q)) =
    (side.placeClass (a := a) (b := b) idle (CapClass.ofDrawing p)).thenDo
      (side.placeClass (a := b) (b := c) idle (CapClass.ofDrawing q))
  simp only [CapClass.thenDo_drawings, placeClass_drawings]
  exact CapClass.sound ⟨side.compareComposition (a := a) (b := b) (c := c) idle p q⟩

/-- Place every drawing beside the fixed idle cap on the selected side. -/
@[expose] def whisker : FixedCap S ⥤ FixedCap S where
  obj a := side.adjoin a idle
  map {a b} f := side.placeClass (a := a) (b := b) idle f
  map_id a := side.placeClass_identity idle a
  map_comp {a b c} f g := side.placeClass_comp (a := a) (b := b) (c := c) idle f g

theorem whisker_drawings (p : FixedDrawing S a.profile b.profile) :
    (side.whisker idle).map (FixedCap.ofDrawing p) =
      FixedCap.ofDrawing (side.placeDrawing p idle) :=
  ActiveStrip.placeClass_drawings side idle p

end Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip
