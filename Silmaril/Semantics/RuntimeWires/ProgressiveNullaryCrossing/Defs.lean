module

public import Silmaril.Semantics.RuntimeWires.ProgressiveNullarySlide.Thms

@[expose] public section

/-!
# Slicing an isolated nullary crossing

A local comparison for Definition 3.2 and Figure 7, toward Lemma 3.4,
Theorem 3.6 and Corollary 3.15 of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5
(pp. 9:6–9:8 and 9:13).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}

/-- Read two isolated events at three actual cuts, using the geometric
wire lists as the source and target. -/
structure TwoEventSlice (d : Diagram S V W .point) (first second : Fin V) (lo mid hi : ℝ) where
  firstEvent : d.EventSlice first lo mid
  secondEvent : d.EventSlice second mid hi

namespace TwoEventSlice

variable {d : Diagram S V W .point} {first second : Fin V} {lo mid hi : ℝ}

def sheet (q : d.TwoEventSlice first second lo mid hi) :
    Sheet S (q.firstEvent.beforeWires.map d.label) (q.secondEvent.afterWires.map d.label) :=
  let first := q.firstEvent
  let second := q.secondEvent
  let seamWord := (second.before_word.symm.trans
    (congrArg (List.map d.label) (first.shared_wires second)).symm).trans first.after_word
  (Sheet.cons first.row ((Sheet.cons second.row (.empty _)).reindex seamWord rfl)).reindex
    first.before_word.symm second.after_word.symm

end TwoEventSlice

namespace NullarySlide

variable {d : Diagram S V W .point} {moved : Fin V} (s : d.NullarySlide moved)

/-- The horizontal side occupied by the moving scalar. -/
inductive Side
  | left
  | right

namespace Side

/-- The vertices in the geometric left-to-right order. -/
def leftVertex {V : ℕ} : Side → Fin V → Fin V → Fin V
  | .left, moved, _ => moved
  | .right, _, other => other

def rightVertex {V : ℕ} : Side → Fin V → Fin V → Fin V
  | .left, _, other => other
  | .right, moved, _ => moved

end Side

/-- A nullary slide past one stationary vertex. The two interior
cuts can be any regular heights strictly between the endpoint events.
The clear travel segment and typed wire/port data come from the slide. -/
structure Crossing (other : Fin V) (side : Side := .left) where
  lowerCut : ℝ
  earlyCut : ℝ
  lateCut : ℝ
  upperCut : ℝ
  horizontal : d.vertexX (side.leftVertex moved other) < d.vertexX (side.rightVertex moved other)
  lower_inside : 0 < lowerCut
  lower_bottom : lowerCut < s.bottom
  bottom_early : s.bottom < earlyCut
  early_other : earlyCut < d.vertexHeight other
  other_late : d.vertexHeight other < lateCut
  late_top : lateCut < s.top
  top_upper : s.top < upperCut
  upper_inside : upperCut < 1
  only : ∀ j, d.vertexHeight j ∈ Set.Icc lowerCut upperCut → j = moved ∨ j = other

namespace Crossing

variable {s} {other : Fin V} {side : Side} (c : s.Crossing other side)

def tied : Diagram S V W .point :=
  s.atHeight (d.vertexHeight other) ⟨(c.bottom_early.trans c.early_other).le,
    (c.other_late.trans c.late_top).le⟩

/-- The three geometric reads in the same slab. Ordered wire IDs, rather
than equality of labels alone, identify their external frontiers. -/
structure Readback where
  tie : c.tied.PairSlice (side.leftVertex moved other) (side.rightVertex moved other) c.lowerCut c.upperCut
  early : s.initial.TwoEventSlice moved other c.lowerCut c.earlyCut c.upperCut
  late : s.terminal.TwoEventSlice other moved c.lowerCut c.lateCut c.upperCut
  early_input : early.firstEvent.beforeWires = tie.inputWires
  early_output : early.secondEvent.afterWires = tie.outputWires
  late_input : late.firstEvent.beforeWires = tie.inputWires
  late_output : late.secondEvent.afterWires = tie.outputWires

namespace Readback

variable {c} (r : c.Readback)

/-- The real tied layer from the two horizontally ordered sides of the pair slice. -/
def tiedSheet : Sheet S r.tie.sourceWord r.tie.targetWord :=
  .cons (r.tie.leftRow.beside r.tie.rightRow) (.empty _)

/-- Transport the independently sliced endpoints to the actual tied frontier words. -/
def earlySheet : Sheet S r.tie.sourceWord r.tie.targetWord :=
  r.early.sheet.reindex (A := r.early.firstEvent.beforeWires.map s.initial.label)
    (B := r.early.secondEvent.afterWires.map s.initial.label)
    (by exact (congrArg (List.map d.label) r.early_input).trans r.tie.input_types)
    (by exact (congrArg (List.map d.label) r.early_output).trans r.tie.output_types)

def lateSheet : Sheet S r.tie.sourceWord r.tie.targetWord :=
  r.late.sheet.reindex (A := r.late.firstEvent.beforeWires.map s.terminal.label)
    (B := r.late.secondEvent.afterWires.map s.terminal.label)
    (by exact (congrArg (List.map d.label) r.late_input).trans r.tie.input_types)
    (by exact (congrArg (List.map d.label) r.late_output).trans r.tie.output_types)

end Readback
end Crossing
end NullarySlide
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
