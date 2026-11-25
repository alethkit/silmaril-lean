module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Wires

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Wire

variable {a m b : ℝ}

/-- Rescale a polygonal wire into a half-height slab. -/
@[expose] noncomputable def halve (w : Wire a b) (offset : ℝ) :
    Wire (halfHeight offset a) (halfHeight offset b) where
  x := w.x ∘ slabHeight offset
  increasing := by exact Proofs.ProgressiveGluing.half_mono offset w.increasing
  continuous := by exact Proofs.ProgressiveGluing.scale_continuous w offset
  polygonal := by exact Proofs.ProgressiveGluing.scale_polygonal w offset

/-- Splice two polygonal strands at an equal endpoint. The shared height
can be a breakpoint, and it remains an interior point of the new wire. -/
@[expose] noncomputable def splice (first : Wire a m) (last : Wire m b) (contact : first.x m = last.x m) :
    Wire a b where
  x := spliceX m first.x last.x
  increasing := first.increasing.trans last.increasing
  continuous := by exact Proofs.ProgressiveGluing.splice_continuous first last contact
  polygonal := by exact Proofs.ProgressiveGluing.splice_polygonal first last contact

theorem splice_x_lower (first : Wire a m) (last : Wire m b) (contact : first.x m = last.x m)
    {h : ℝ} (below : h ≤ m) : (first.splice last contact).x h = first.x h :=
  Proofs.ProgressiveGluing.splice_left below

theorem splice_x_upper (first : Wire a m) (last : Wire m b) (contact : first.x m = last.x m)
    {h : ℝ} (above : m ≤ h) : (first.splice last contact).x h = last.x h :=
  Proofs.ProgressiveGluing.splice_right contact above

end Silmaril.RuntimeWires.ProgressiveGraph.Wire

namespace Silmaril.RuntimeWires.ProgressiveGraph.Wire

/-- Re-express equal endpoints without changing the horizontal coordinate. -/
@[expose] def atBounds {a b c d : ℝ} (wire : Wire a b) (lo : a = c) (hi : b = d) : Wire c d where
  x := wire.x
  increasing := by simpa only [← lo, ← hi] using wire.increasing
  continuous := by simpa only [← lo, ← hi] using wire.continuous
  polygonal := by simpa only [← lo, ← hi] using wire.polygonal

end Silmaril.RuntimeWires.ProgressiveGraph.Wire

namespace Silmaril.RuntimeWires.ProgressiveGraph

theorem halfHeight_strictMono (offset : ℝ) : StrictMono (halfHeight offset) :=
  Proofs.ProgressiveGluing.half_mono offset

end Silmaril.RuntimeWires.ProgressiveGraph
