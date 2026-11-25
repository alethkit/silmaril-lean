module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Gluing

public section

/-!
# Units for fixed-contact vertical gluing

An ambient homeomorphism expands a vertex-free cap neighborhood to make
space for the identity and collar slabs. A horizontal ordered-knot
homeomorphism maps all cap strands there, and affine placement maps the
rest of the drawing. The two original caps stay fixed pointwise.
This gives unit laws for the fixed-contact endpoint classes of the
vertical part of Lemma 3.4 and Figure 7 in Román and Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5, p. 9:7.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}

theorem CapProfile.empty_inside : (CapProfile.empty : CapProfile O).Inside :=
  fun i => i.elim0

namespace FixedDrawing

theorem bottom_inside (p : FixedDrawing S a b) : a.Inside := Proofs.CapUnits.bottom_inside p
theorem top_inside (p : FixedDrawing S a b) : b.Inside := Proofs.CapUnits.top_inside p

/-- A cap admits a drawing with identical boundary profiles exactly when
all its horizontal coordinates lie in the open square. -/
theorem exists_identity_iff : Nonempty (FixedDrawing S a a) ↔ a.Inside :=
  ⟨fun ⟨d⟩ => d.bottom_inside, fun h => ⟨identity S a h⟩⟩

theorem identity_x (h : a.Inside) (i : Fin a.size) (y : ℝ) :
    (identity S a h).drawing.x i y = a.x i :=
  Proofs.CapUnits.identity_x h i y

/-- Make room for the lower identity and collar while preserving the full
traces, labeled incidence and ordered ports of the original drawing. -/
noncomputable def compareLeftUnit (p : FixedDrawing S a b) (h : a.Inside) :
    p.drawing.CapComparison (((identity S a h).thenDo p).drawing) :=
  Proofs.CapUnits.Window.compare (Proofs.CapUnits.leftPlaced p h)

/-- The analogous ambient comparison at the upper cap. -/
noncomputable def compareRightUnit (p : FixedDrawing S a b) (h : b.Inside) :
    p.drawing.CapComparison ((p.thenDo (identity S b h)).drawing) :=
  Proofs.CapUnits.Window.compare (Proofs.CapUnits.rightPlaced p h)

theorem identity_thenDo (p : FixedDrawing S a b) (h : a.Inside) :
    ((identity S a h).thenDo p).Equivalent p :=
  Equivalent.symm ⟨p.compareLeftUnit h⟩

theorem thenDo_identity (p : FixedDrawing S a b) (h : b.Inside) :
    (p.thenDo (identity S b h)).Equivalent p :=
  Equivalent.symm ⟨p.compareRightUnit h⟩

end FixedDrawing

namespace CapClass

noncomputable def identity (S : Signature.{u,v} O) (a : CapProfile O) (h : a.Inside) :
    CapClass S a a :=
  ofDrawing (FixedDrawing.identity S a h)

theorem identity_thenDo (p : CapClass S a b) (h : a.Inside) :
    (identity S a h).thenDo p = p :=
  Quotient.inductionOn p fun d => (thenDo_drawings _ _).trans (sound (d.identity_thenDo h))

theorem thenDo_identity (p : CapClass S a b) (h : b.Inside) :
    p.thenDo (identity S b h) = p :=
  Quotient.inductionOn p fun d => (thenDo_drawings _ _).trans (sound (d.thenDo_identity h))

end CapClass
end Silmaril.RuntimeWires.ProgressiveGraph
