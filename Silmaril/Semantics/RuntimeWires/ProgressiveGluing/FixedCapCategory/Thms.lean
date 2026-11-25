module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.FixedCapCategory.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Thms

public section

/-!
# The fixed-contact vertical category

This packages the vertical construction in Lemma 3.4 and Figure 7 of
Román and Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5, p. 9:7, for admissible fixed-contact profiles.

Horizontal whiskering requires progressive, nonintersecting placement of
the active drawing and idle strands in disjoint strips, with ordered
typed cap concatenation. To descend placement to the existing classes,
confine the horizontal component of a comparison to the active strip and
use the same height reparametrization on the idle strands. Both the map
and its inverse must paste continuously at the strip wall and fix the
outer caps. Functoriality then requires geometric comparisons with the
straight identity and with actual collared composition, including its
splice wire renamings.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c : FixedCap S}

/-- The identity uses only the profile. Any proof of admissibility gives
the same straight drawing class. -/
theorem id_eq (a : FixedCap S) (h : a.profile.Inside) :
    𝟙 a = ofDrawing (FixedDrawing.identity S a.profile h) := by rfl

/-- The composite on representatives is the class of their actual collared
gluing. -/
theorem comp_drawings (f : FixedDrawing S a.profile b.profile)
    (g : FixedDrawing S b.profile c.profile) :
    ofDrawing f ≫ ofDrawing g = ofDrawing (f.thenDo g) :=
  CapClass.thenDo_drawings f g

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap
