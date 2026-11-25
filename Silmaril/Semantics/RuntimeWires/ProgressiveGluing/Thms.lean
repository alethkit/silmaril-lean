module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Geometry
public import Silmaril.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Readback
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Traces

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.VerticalMatch

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : ProgressiveGraph.Diagram S L W .point}
variable {upper : ProgressiveGraph.Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

/-- A spliced strand consists exactly of the rescaled original traces. -/
theorem glue_trace (w : Fin W) :
    (m.glue.wire w).trace =
      (fun p : ℝ × ℝ => (p.1, halfHeight 0 p.2)) '' (lower.wire w).trace ∪
      (fun p : ℝ × ℝ => (p.1, halfHeight 1 p.2)) '' (upper.wire w).trace :=
  Proofs.ProgressiveGluing.glue_trace m w

/-- The internal join is a regular cut and every spliced wire crosses it. -/
theorem join_regular : m.glue.Regular (1 / 2) :=
  Proofs.ProgressiveGluing.join_regular m

theorem cut_below {h : ℝ} {ids : List (Fin W)} (below : h < 1) (cut : lower.OrderedCut h ids) :
    m.glue.OrderedCut (halfHeight 0 h) ids :=
  Proofs.ProgressiveGluing.cut_left m below cut

theorem cut_above {h : ℝ} {ids : List (Fin W)} (above : 0 < h) (cut : upper.OrderedCut h ids) :
    m.glue.OrderedCut (halfHeight 1 h) ids :=
  Proofs.ProgressiveGluing.cut_right m above cut

section TwoEvents

variable {lower upper : ProgressiveGraph.Diagram S 1 W .point}
variable (m : lower.VerticalMatch upper) {a b c d : ℝ}

theorem isolates_lower (iso : lower.Isolates 0 a b) :
    m.glue.Isolates (Fin.castAdd 1 (0 : Fin 1)) (halfHeight 0 a) (1 / 2) :=
  Proofs.ProgressiveGluing.lower_isolates m iso

theorem isolates_upper (iso : upper.Isolates 0 c d) :
    m.glue.Isolates (Fin.natAdd 1 (0 : Fin 1)) (1 / 2) (halfHeight 1 d) :=
  Proofs.ProgressiveGluing.upper_isolates m iso

/-- With one vertex in each operand, slicing the glued diagram at the
rescaled exterior cuts and at the actual join reads the concatenation.
The transports use the ordered wire IDs at the exterior cuts and the join. -/
theorem concat_readback (e : lower.EventSlice 0 a b) (f : upper.EventSlice 0 c d)
    (ea : lower.Isolates 0 a b) (fa : upper.Isolates 0 c d)
    (g : m.glue.TwoEventSlice (Fin.castAdd 1 (0 : Fin 1)) (Fin.natAdd 1 (0 : Fin 1))
      (halfHeight 0 a) (1 / 2) (halfHeight 1 d)) :
    ∃ (first : g.firstEvent.beforeWires.map m.glue.label = e.beforeWires.map lower.label)
      (last : g.secondEvent.afterWires.map m.glue.label = f.afterWires.map upper.label)
      (join : f.beforeWires.map upper.label = e.afterWires.map lower.label),
      g.sheet.reindex first last = (Sheet.cons e.cutRow (.empty _)).thenDo
        ((Sheet.cons f.cutRow (.empty _)).reindex join rfl) := by
  obtain ⟨r, first, last, join, eq⟩ := Proofs.ProgressiveGluing.concat_readback m e f ea fa
  cases g.unique r
  exact ⟨first, last, join, eq⟩

end TwoEvents
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.VerticalMatch
