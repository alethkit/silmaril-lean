module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGraph.Readback

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}

theorem ordered_cut_exists (d : Diagram S V W) (h : ℝ) : ∃ wires, d.OrderedCut h wires :=
  Proofs.ProgressiveGraph.ordered_cut_exists d h

theorem ordered_cut_unique {h : ℝ} {a b : List (Fin W)}
    (ha : d.OrderedCut h a) (hb : d.OrderedCut h b) : a = b :=
  Proofs.ProgressiveGraph.ordered_cut_unique d ha hb

/-- A regular cut enumerates exactly the intersections of the wire traces
with that height. -/
theorem regular_trace {h : ℝ} (reg : d.Regular h) {wires : List (Fin W)}
    (cut : d.OrderedCut h wires) :
    d.wireTrace ∩ {p | p.2 = h} = {p | p.2 = h ∧ p.1 ∈ wires.map (fun w => d.x w h)} :=
  Proofs.ProgressiveGraph.regular_trace d reg cut

/-- Two strands with no common point on a closed height interval retain
their horizontal order from one end to the other. -/
theorem order_across {a b : ℝ} {w z : Fin W}
    (cover : ∀ h ∈ Set.uIcc a b, d.covers w h ∧ d.covers z h)
    (separate : ∀ h ∈ Set.uIcc a b, d.x w h ≠ d.x z h)
    (ordered : d.x w a < d.x z a) : d.x w b < d.x z b :=
  Proofs.ProgressiveGraph.order_transport d cover separate ordered

/-- An isolated vertex changes exactly its contiguous block of wires.
The unchanged parts keep the same wire indices in the same order,
including when either or both incident blocks are empty. -/
theorem single_event {v : Fin V} {lo hi : ℝ} (iso : d.Isolates v lo hi) :
    Nonempty (d.EventSlice v lo hi) :=
  Proofs.ProgressiveGraph.single_event d iso

namespace EventSlice

variable {v z : Fin V} {lo mid hi : ℝ}

theorem before_word (s : d.EventSlice v lo hi) :
    s.beforeWires.map d.label =
      s.left.map d.label ++ (S.source (d.generator v) ++ s.right.map d.label) :=
  Proofs.ProgressiveGraph.before_word s

theorem after_word (s : d.EventSlice v lo hi) :
    s.afterWires.map d.label =
      s.left.map d.label ++ (S.target (d.generator v) ++ s.right.map d.label) :=
  Proofs.ProgressiveGraph.after_word s

/-- Read the row at the words obtained from the actual wire indices. -/
@[expose] def cutRow (s : d.EventSlice v lo hi) :
    Sliced.Row S (s.beforeWires.map d.label) (s.afterWires.map d.label) :=
  (congrArg₂ (Sliced.Row S) s.before_word s.after_word).symm.mp s.row

/-- Two consecutive event slices agree on the full ordered wire list at
their shared seam. -/
theorem shared_wires (s : d.EventSlice v lo mid) (t : d.EventSlice z mid hi) :
    s.afterWires = t.beforeWires :=
  ordered_cut_unique s.after t.before

/-- Prepend an event to a sheet read at the same output word. -/
def prepend (s : d.EventSlice v lo hi) {B : List O}
    (tail : Sliced.Sheet S (s.afterWires.map d.label) B) :
    Sliced.Sheet S (s.beforeWires.map d.label) B :=
  .cons s.cutRow tail

/-- Prepend the event to a continuation at the next event's lower cut. -/
def prependAtSeam (s : d.EventSlice v lo mid) (t : d.EventSlice z mid hi) {B : List O}
    (tail : Sliced.Sheet S (t.beforeWires.map d.label) B) :
    Sliced.Sheet S (s.beforeWires.map d.label) B :=
  s.prepend ((congrArg (fun wires => Sliced.Sheet S (wires.map d.label) B)
    (s.shared_wires t)).symm.mp tail)

end EventSlice
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
