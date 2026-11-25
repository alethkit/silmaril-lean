module

public import Mathlib.CategoryTheory.Iso
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Comparison
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching

public noncomputable section

/-!
# Recoordination of fixed caps

Profiles with the same ordered word are isomorphic in the fixed-contact
category. Their morphisms are actual straight interpolating drawings.
The proof compares any two vertex-free drawings over the same outer
caps. Every height sees the same ordered strands, and an increasing
piecewise-affine homeomorphism of each horizontal line matches the
corresponding strand points. The inverse exchanges the knot lists.
The comparison fixes the caps and the exterior of the unit square.

The cocycle allows one to choose a normalization for each ordered word
or to insert coordinate changes between different horizontal placements.
Coherence with whiskering requires additional naturality equations.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

namespace FixedDrawing

variable {a b : CapProfile O} (p q : FixedDrawing S a b)
variable (hp : p.vertices = 0) (hq : q.vertices = 0)

/-- Compare whole through-strand drawings over the same fixed profiles
using the order of the bottom cap slots. -/
def compareVertexFree : p.drawing.CapComparison q.drawing :=
  Proofs.CapRecoordination.compare p q hp hq

theorem compareVertexFree_height (z : ℝ × ℝ) :
    ((p.compareVertexFree q hp hq).map.plane z).2 = z.2 := by rfl

theorem compareVertexFree_increasing (y : ℝ) :
    StrictMono (fun x => ((p.compareVertexFree q hp hq).map.plane (x, y)).1) :=
  Proofs.CapRecoordination.increasing_fibre p hp q hq y

theorem compareVertexFree_outside_sides (z : ℝ × ℝ) (h : z.1 ≤ 0 ∨ 1 ≤ z.1) :
    (p.compareVertexFree q hp hq).map.plane z = z :=
  Proofs.CapRecoordination.ambient_outside_sides p hp q hq z h

theorem compareVertexFree_point (i : Fin a.size) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (p.compareVertexFree q hp hq).map.plane (p.drawing.x (p.input i).val y, y) =
      (q.drawing.x (q.input i).val y, y) :=
  Proofs.CapRecoordination.ambient_point p hp q hq i hy

theorem compareVertexFree_input (i : Fin a.size) :
    (p.compareVertexFree q hp hq).incidence.wire (p.input i).val = (q.input i).val :=
  Proofs.CapRecoordination.wire_at_input p q hp hq i

theorem compareVertexFree_output (i : Fin b.size) :
    (p.compareVertexFree q hp hq).incidence.wire (p.output i).val = (q.output i).val :=
  congrArg Subtype.val (Proofs.CapClasses.output_slot (p.compareVertexFree q hp hq) i)

end FixedDrawing

namespace FixedCap

variable {a b c : FixedCap S}

theorem interpolation_x (h : a.types = b.types) (i : Fin a.profile.size) (y : ℝ) :
    (interpolationDrawing h).drawing.x i y =
      interpolate (a.profile.x i) (b.profile.x (recoordinationSlots h i)) y :=
  (interpolationSpec h).drawing_x i y

theorem recoordinate_refl (a : FixedCap S) :
    recoordinate (a := a) (b := a) rfl = 𝟙 a := by
  rw [id_eq a a.inside]
  exact CapClass.sound ⟨FixedDrawing.compareVertexFree _ _ rfl rfl⟩

/-- Vertical gluing of two interpolating drawings gives the same class as
the direct interpolation between the remaining caps. -/
theorem recoordinate_comp (h : a.types = b.types) (k : b.types = c.types) :
    recoordinate h ≫ recoordinate k = recoordinate (h.trans k) := by
  simp only [recoordinate, comp_drawings]
  exact CapClass.sound ⟨FixedDrawing.compareVertexFree _ _ (by rfl) rfl⟩

/-- A change of coordinates with inverse given by the reverse straight interpolation. -/
def recoordinateIso (h : a.types = b.types) : a ≅ b where
  hom := recoordinate h
  inv := recoordinate h.symm
  hom_inv_id := (recoordinate_comp h h.symm).trans (recoordinate_refl a)
  inv_hom_id := (recoordinate_comp h.symm h).trans (recoordinate_refl b)

end FixedCap

end Silmaril.RuntimeWires.ProgressiveGraph
