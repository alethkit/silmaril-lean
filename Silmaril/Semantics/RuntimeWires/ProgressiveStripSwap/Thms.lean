module

public import Silmaril.Semantics.RuntimeWires.ProgressiveStripSwap.Defs
import all Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveStripSwap.Frames
import Mathlib.Tactic.NormNum

public noncomputable section

/-!
# Swapping two isolated vertices by a progressive ambient isotopy

Within each strip core, a strictly increasing piecewise-affine height map
moves its one vertex and its incident strands. The ambient maps taper to the
identity at the strip boundaries and fix both caps. The inverse exchanges the
source and target height knots on each vertical fibre. The strip hypotheses
put all geometry in the cores or in the fixed exterior. This is one geometric
move toward the interchange in Lemma 3.4 of Román and Sobociński,
arXiv:2305.06075v5.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.IsolatedStripSwap

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : ProgressiveGraph.Diagram S V W .point}

/-- An ambient path through progressive polygonal drawings, starting at the
identity and retaining exact full traces and typed incidence. -/
def isotopy (s : d.IsolatedStripSwap) : d.ProgressiveIsotopy :=
  Proofs.ProgressiveStripSwap.isotopy s

variable (s : d.IsolatedStripSwap) (t : SlabIsotopy.Time)

theorem left_height : (s.isotopy.drawing t).vertexHeight s.left =
    interpolate (d.vertexHeight s.left) (d.vertexHeight s.right) t.val :=
  Proofs.ProgressiveStripSwap.left_height s t

theorem right_height : (s.isotopy.drawing t).vertexHeight s.right =
    interpolate (d.vertexHeight s.right) (d.vertexHeight s.left) t.val :=
  Proofs.ProgressiveStripSwap.right_height s t

/-- The simultaneous-height frame is still a valid point drawing. -/
theorem midpoint_height :
    let t : SlabIsotopy.Time := ⟨1 / 2, by norm_num [Set.mem_Icc]⟩
    (s.isotopy.drawing t).vertexHeight s.left = (s.isotopy.drawing t).vertexHeight s.right := by
  dsimp only
  erw [left_height, right_height]
  unfold interpolate
  ring

/-- The endpoint interchanges the two actual heights. -/
theorem final_height :
    let t : SlabIsotopy.Time := ⟨1, zero_le_one, le_rfl⟩
    (s.isotopy.drawing t).vertexHeight s.left = d.vertexHeight s.right ∧
      (s.isotopy.drawing t).vertexHeight s.right = d.vertexHeight s.left := by
  dsimp only
  erw [left_height, right_height]
  simp [interpolate]

theorem final_reversed :
    let t : SlabIsotopy.Time := ⟨1, zero_le_one, le_rfl⟩
    (s.isotopy.drawing t).vertexHeight s.right < (s.isotopy.drawing t).vertexHeight s.left := by
  obtain ⟨left, right⟩ := s.final_height
  dsimp only
  rw [left, right]
  exact s.ordered

/-- The ambient support lies inside the two open strips and the open height slab. -/
theorem fixed_exterior (z : ℝ × ℝ) (hz : z.1 ∈ s.strips.region .exterior) :
    s.isotopy.frame t z = z :=
  Proofs.ProgressiveStripSwap.fixed_exterior s t z hz

theorem exterior_trace (w : Fin W) (h : s.wireRegion w = .exterior) :
    ((s.isotopy.drawing t).wire w).trace = (d.wire w).trace :=
  Proofs.ProgressiveStripSwap.exterior_wire s t w h

theorem fixed_other_vertex (j : Fin V) (left : j ≠ s.left) (right : j ≠ s.right) :
    ((s.isotopy.drawing t).vertexX j, (s.isotopy.drawing t).vertexHeight j) =
      (d.vertexX j, d.vertexHeight j) := by
  have mem := s.vertex_mem j
  rw [s.other_region j left right] at mem
  exact (s.isotopy.vertex t j).symm.trans (s.fixed_exterior t _ mem)

/-- Outer contacts are pointwise fixed throughout the ambient path. -/
theorem cap_x (w : Fin W) (y : ℝ) (hy : y ≤ 0 ∨ 1 ≤ y) :
    (s.isotopy.drawing t).x w y = d.x w y :=
  Proofs.ProgressiveStripSwap.cap_x s t w y hy

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.IsolatedStripSwap

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedDrawing

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}

/-- The isotopy frames keep the same prescribed ordered and typed caps. -/
def stripSwapAt (p : FixedDrawing S a b) (s : p.drawing.IsolatedStripSwap) (t : SlabIsotopy.Time) :
    FixedDrawing S a b := Proofs.ProgressiveStripSwap.fixedDrawingAt p s t

theorem stripSwapAt_drawing (p : FixedDrawing S a b) (s : p.drawing.IsolatedStripSwap) (t : SlabIsotopy.Time) :
    HEq (p.stripSwapAt s t).drawing (s.isotopy.drawing t) := by rfl

end Silmaril.RuntimeWires.ProgressiveGraph.FixedDrawing
