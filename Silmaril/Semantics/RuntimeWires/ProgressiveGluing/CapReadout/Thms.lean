module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Defs
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Category
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.FixedCapCategory.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Laws

public noncomputable section

/-!
# Reading fixed-contact drawings as sliced diagrams

The sweep reads the geometry before passing to the existing seam quotient.
A cap-relative comparison carries event heights by one increasing map
and preserves the horizontal order of active slots on every level.
This gives the vertical part of the comparison toward Lemma 3.4 and
Theorem 3.6 of *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory
open Sliced (SeamHom Sheet)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c : CapProfile O}

namespace FixedDrawing

/-- Arbitrary valid cuts in cap-equivalent drawings read the same typed
sheet after indexing the boundaries by their prescribed cap words. -/
theorem readSheetAt_comparison {p q : FixedDrawing S a b}
    (h : p.drawing.CapComparison q.drawing) (s : p.drawing.LayerSweep) (t : q.drawing.LayerSweep) :
    p.readSheetAt s = q.readSheetAt t := by
  exact Proofs.CapReadout.readSheetAt_comparison h s t

theorem readSheet_congr {p q : FixedDrawing S a b} (h : p.Equivalent q) :
    p.readSheet = q.readSheet :=
  h.elim fun h => readSheetAt_comparison h p.drawing.layerSweep q.drawing.layerSweep

theorem readSerialAt_seam (p : FixedDrawing S a b) (s : p.drawing.LayerSweep) (order : s.Schedule) :
    Sheet.SeamEquivalent (p.readSerialAt s order) (p.readSheetAt s) := by
  exact (s.serial_seam order).reindex _ _

/-- The actual collared gluing reads as typed concatenation. -/
theorem readSheet_thenDo (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    (p.thenDo q).readSheet = p.readSheet.thenDo q.readSheet := by
  exact Proofs.CapReadout.readSheet_thenDo p q

/-- A vertex-free drawing reads as identity at the common boundary word. -/
theorem readSheet_vertexFree (p : FixedDrawing S a b) (vertices : p.vertices = 0)
    (word : List.ofFn a.label = List.ofFn b.label) :
    p.readSheet = (Sheet.empty (S := S) (List.ofFn a.label)).reindex rfl word := by
  exact Proofs.CapReadout.readSheet_vertexFree p vertices word

end FixedDrawing

namespace CapClass

/-- Read a geometric class in the existing quotient by sliced seam moves. -/
def readout (p : CapClass S a b) : SeamHom S (List.ofFn a.label) (List.ofFn b.label) := by
  change Quotient (FixedDrawing.setoid S a b) at p
  exact Quotient.lift (fun d : FixedDrawing S a b => SeamHom.ofSheet d.readSheet)
    (fun _ _ h => congrArg SeamHom.ofSheet (FixedDrawing.readSheet_congr h)) p

theorem readout_drawings (p : FixedDrawing S a b) :
    (ofDrawing p).readout = SeamHom.ofSheet p.readSheet := by rfl

theorem readout_thenDo (p : CapClass S a b) (q : CapClass S b c) :
    (p.thenDo q).readout = p.readout.comp q.readout := by
  refine Quotient.inductionOn₂ p q fun d e => ?_
  change (thenDo (ofDrawing d) (ofDrawing e)).readout = _
  rw [thenDo_drawings]
  exact congrArg SeamHom.ofSheet (d.readSheet_thenDo e)

theorem readout_identity (h : a.Inside) :
    (identity S a h).readout = SeamHom.id (List.ofFn a.label) := by
  exact congrArg SeamHom.ofSheet ((FixedDrawing.identity S a h).readSheet_vertexFree rfl rfl)

end CapClass

namespace FixedCap

/-- The vertical readout functor from fixed-contact geometry to the
existing category of seam classes. -/
@[expose] def toSliced (S : Signature.{u,v} O) : FixedCap S ⥤ Sliced.Presented S where
  obj a := ⟨a.types⟩
  map f := CapClass.readout f
  map_id a := CapClass.readout_identity a.inside
  map_comp f g := CapClass.readout_thenDo f g

theorem toSliced_drawings {a b : FixedCap S} (p : FixedDrawing S a.profile b.profile) :
    (toSliced S).map (ofDrawing p) = SeamHom.ofSheet p.readSheet :=
  CapClass.readout_drawings p

theorem toSliced_recoordinate {a b : FixedCap S} (h : a.types = b.types) :
    (toSliced S).map (recoordinate h) =
      SeamHom.ofSheet ((Sheet.empty (S := S) a.types).reindex rfl h) :=
  congrArg SeamHom.ofSheet ((interpolationDrawing h).readSheet_vertexFree rfl h)

end FixedCap
end Silmaril.RuntimeWires.ProgressiveGraph
