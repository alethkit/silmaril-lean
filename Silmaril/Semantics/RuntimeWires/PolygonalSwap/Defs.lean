module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Realization
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Progressive swap of two disjoint boxes

This local deformation concerns Definition 3.2 and Figure 7 (pp. 9:6–9:7)
of Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal
Categories*, arXiv:2305.06075v5. It compares the two orders of slicing a
row of independent boxes, as a step toward the geometric comparison in
Lemma 3.4 and Theorem 3.6 (pp. 9:7–9:8).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Polygonal

universe u v

abbrev SwapTime := Set.Icc (0 : ℝ) 1

def swapStart : SwapTime := ⟨0, le_rfl, zero_le_one⟩

def swapFinish : SwapTime := ⟨1, zero_le_one, le_rfl⟩

/-- A unit-height box whose lower edge is between heights 1 and 4. -/
abbrev BoxAltitude := Set.Icc (1 : ℝ) 4

def referenceAltitude : BoxAltitude := ⟨1, le_rfl, by linarith⟩

noncomputable def swapMiddle : SwapTime := ⟨(1 : ℝ) / 2, by constructor <;> linarith⟩

namespace BoxAltitude

def inputs (h : BoxAltitude) : Slab := ⟨0, h, zero_lt_one.trans_le h.property.1⟩

def body (h : BoxAltitude) : Slab := Slab.unit h

def outputs (h : BoxAltitude) : Slab := ⟨h.val + 1, 6, by linarith [h.property.2]⟩

end BoxAltitude

variable {O : Type u} {S : Signature.{u,v} O} {floor : ℝ} {e f : S.Edge}

/-- A generator body or one of its individually labeled incident wires. -/
inductive BoxCell (S : Signature.{u,v} O) (e : S.Edge) where
  | body
  | input (i : Fin (S.source e).length)
  | output (i : Fin (S.target e).length)

namespace Box

/-- Each external port is vertically aligned with its port on the box. -/
def incoming (b : Box S floor e) (h : BoxAltitude) (i : Fin (S.source e).length) :
    Strand (BoxAltitude.inputs h) :=
  connector (BoxAltitude.inputs h) b.input b.input i

def outgoing (b : Box S floor e) (h : BoxAltitude) (i : Fin (S.target e).length) :
    Strand (BoxAltitude.outputs h) :=
  connector (BoxAltitude.outputs h) b.output b.output i

def cell (b : Box S floor e) (h : BoxAltitude) : BoxCell S e → Set Point
  | .body => b.trace (BoxAltitude.body h)
  | .input i => (b.incoming h i).trace
  | .output i => (b.outgoing h i).trace

/-- A box with its incident input and output wires extending to the two fixed caps. -/
def column (b : Box S floor e) (h : BoxAltitude) : Set Point :=
  ⋃ c, b.cell h c

end Box

/-- Two boxes in separate horizontal slots. The heights of their traces
can vary independently. Vertex labels and port coordinates are fixed. -/
structure BoxPair (S : Signature.{u,v} O) (floor : ℝ) (e f : S.Edge) where
  first : Box S floor e
  second : Box S first.right f

namespace BoxPair

variable (d : BoxPair S floor e f)

def leftSide : ℝ := d.first.left - 1

def rightSide : ℝ := d.second.right + 1

def rectangle : Set Point := Set.Icc d.leftSide d.rightSide ×ˢ Set.Icc 0 6

def OnBoundary (p : Point) : Prop :=
  p.1 = d.leftSide ∨ p.1 = d.rightSide ∨ p.2 = 0 ∨ p.2 = 6

def firstAltitude (t : SwapTime) : BoxAltitude :=
  ⟨1 + 3 * t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩

def secondAltitude (t : SwapTime) : BoxAltitude :=
  ⟨4 - 3 * t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩

def snapshot (t : SwapTime) : Set Point :=
  d.first.column (firstAltitude t) ∪ d.second.column (secondAltitude t)

/-- A continuous ramp which is zero up to `a` and one from `b` onward when `a < b`. -/
noncomputable def ramp (a b x : ℝ) : ℝ := max 0 (min 1 ((x - a) / (b - a)))

/-- Vary the altitude across the slots and return to the reference altitude
at both vertical sides of the outer rectangle. -/
noncomputable def altitude (t : SwapTime) (x : ℝ) : ℝ :=
  let between := ramp d.first.right d.second.left x
  1 + ((firstAltitude t).val - 1) * ramp d.leftSide d.first.left x * (1 - between) +
    ((secondAltitude t).val - 1) * between * (1 - ramp d.second.right d.rightSide x)

/-- Piecewise affine height rescaling, with knots at 0, 1, 2, 6 sent to
0, `h`, `h + 1`, 6. For 1 ≤ h ≤ 4 all three slopes are positive. -/
noncomputable def rescale (h y : ℝ) : ℝ :=
  h * min y 1 + (min (max y 1) 2 - 1) + ((5 - h) / 4) * max (y - 2) 0

/-- Place the reference picture whose boxes both span heights 1 and 2
into one frame of the swap. Horizontal coordinates are unchanged. -/
noncomputable def frame (t : SwapTime) (p : Point) : Point :=
  (p.1, rescale (d.altitude t p.1) p.2)

open Silmaril.RuntimeWires.Sliced

/-- The two-row schedule read when the first box is below height 3. -/
def firstThenSecond (S : Signature.{u,v} O) (e f : S.Edge) :
    Sheet S (S.source e ++ (S.source f ++ [])) (S.target e ++ (S.target f ++ [])) :=
  .cons (.box e (Row.pass (S.source f) .empty))
    (.cons (Row.pass (S.target e) (.box f .empty)) (.empty _))

/-- The two-row schedule read when the second box is below height 3. -/
def secondThenFirst (S : Signature.{u,v} O) (e f : S.Edge) :
    Sheet S (S.source e ++ (S.source f ++ [])) (S.target e ++ (S.target f ++ [])) :=
  .cons (Row.pass (S.source e) (.box f .empty))
    (.cons (.box e (Row.pass (S.target f) .empty)) (.empty _))

/-- The ordered ports at height 3 in the first schedule. -/
def firstSeam : Frontier (S.target e ++ (S.source f ++ [])) :=
  let p := d.first.output.append d.second.input (fun x hx y hy =>
    (d.first.output_inside x hx).2.trans (d.second.left_bound.trans (d.second.input_inside y hy).1))
  ⟨p.positions, by simpa using p.length_eq, p.ordered⟩

/-- The ordered ports at height 3 in the second schedule. -/
def secondSeam : Frontier (S.source e ++ (S.target f ++ [])) :=
  let p := d.first.input.append d.second.output (fun x hx y hy =>
    (d.first.input_inside x hx).2.trans (d.second.left_bound.trans (d.second.output_inside y hy).1))
  ⟨p.positions, by simpa using p.length_eq, p.ordered⟩

end BoxPair
end Silmaril.RuntimeWires.Polygonal
