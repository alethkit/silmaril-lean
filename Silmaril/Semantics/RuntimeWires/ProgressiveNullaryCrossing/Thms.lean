module

public import Silmaril.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Comparison

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}

/-- At fixed cuts the coordinates determine both ordered event slices. -/
theorem TwoEventSlice.unique {d : ProgressiveGraph.Diagram S V W .point} {i j : Fin V} {lo mid hi : ℝ}
    (p q : d.TwoEventSlice i j lo mid hi) : p = q :=
  Proofs.ProgressiveNullaryCrossing.endpoint_unique p q

namespace NullarySlide.Crossing

variable {d : ProgressiveGraph.Diagram S V W .point} {moved other : Fin V}
variable {s : d.NullarySlide moved} {side : NullarySlide.Side} (c : s.Crossing other side)

/-- The tied drawing is a frame of the continuous slide. -/
theorem tied_frame : ∃ t, s.frame t = c.tied :=
  Proofs.ProgressiveNullaryCrossing.tied_frame c

/-- The existing single-event and simultaneous-pair slicers read all three frames.
The exact ordered wire IDs at the ends of the slab agree. -/
theorem exists_readback : Nonempty c.Readback :=
  Proofs.ProgressiveNullaryCrossing.exists_readback c

namespace Readback

variable {c} (r : c.Readback)

/-- Each independently sliced endpoint is a single split of the tied sheet.
The two splits use opposite event orders at the same horizontal slots. -/
theorem splits :
    Sheet.Move S r.tiedSheet r.earlySheet ∧ Sheet.Move S r.tiedSheet r.lateSheet :=
  Proofs.ProgressiveNullaryCrossing.compare_readbacks c r

/-- The order reversal is an inverse split followed by the opposite split. -/
theorem seam : Sheet.SeamEquivalent r.earlySheet r.lateSheet :=
  .trans _ r.tiedSheet _ (.symm _ _ (.rel _ _ r.splits.1)) (.rel _ _ r.splits.2)

end Readback
end NullarySlide.Crossing
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
