module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Layout
public import Silmaril.Semantics.RuntimeWires.Sliced.Defs
import Mathlib.Tactic.Linarith

@[expose] public section

namespace Silmaril.RuntimeWires.Polygonal

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- Successive ports are one unit apart. -/
def Frontier.grid (A : List O) (first : ℝ) : Frontier A :=
  Frontier.ofCoordinates (fun i => first + (i.val : ℝ)) (by
    intro i j h
    have ordered : (i.val : ℝ) < (j.val : ℝ) := Nat.cast_lt.mpr h
    exact add_lt_add_right ordered first)

private theorem grid_inside {A : List O} (floor : ℝ) (width : ℕ) (h : A.length ≤ width)
    (x : ℝ) (hx : x ∈ (Frontier.grid A (floor + 2)).positions) :
    floor + 1 < x ∧ x < floor + 2 + (width : ℝ) := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  have lo : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hi : (i.val : ℝ) < (width : ℝ) := Nat.cast_lt.mpr (i.isLt.trans_le h)
  constructor <;> linarith

def Through.vertical (floor : ℝ) : Through floor where
  limit := floor + 2
  start := floor + 1
  finish := floor + 1
  start_left := by linarith
  start_right := by linarith
  finish_left := by linarith
  finish_right := by linarith

/-- A box occupies a slot wide enough for either port list. Its width stays
positive even for a generator with neither inputs nor outputs. -/
def Box.onGrid (S : Signature.{u,v} O) (floor : ℝ) (e : S.Edge) : Box S floor e where
  left := floor + 1
  right := floor + 2 + (Nat.max (S.source e).length (S.target e).length : ℝ)
  left_bound := by linarith
  width := by
    have h : (0 : ℝ) ≤ (Nat.max (S.source e).length (S.target e).length : ℝ) := Nat.cast_nonneg _
    linarith
  input := Frontier.grid (S.source e) (floor + 2)
  output := Frontier.grid (S.target e) (floor + 2)
  input_inside := by exact grid_inside floor _ (Nat.le_max_left _ _)
  output_inside := by exact grid_inside floor _ (Nat.le_max_right _ _)

namespace Layer

/-- Read the left-to-right cells of a geometric layer. -/
def readRow : {floor : ℝ} → {A B : List O} → Layer S floor A B → Row S A B
  | _, _, _, .empty _ => .empty
  | _, _, _, .wire label _ rest => .wire label (readRow rest)
  | _, _, _, .box e _ rest => .box e (readRow rest)

/-- Lay out every row using disjoint slots of sufficient width. -/
def realize (floor : ℝ) : {A B : List O} → Row S A B → Layer S floor A B
  | _, _, .empty => .empty floor
  | _, _, .wire label rest =>
    .wire label (Through.vertical floor) (realize (Through.vertical floor).limit rest)
  | _, _, .box e rest =>
    .box e (Box.onGrid S floor e) (realize (Box.onGrid S floor e).right rest)

end Layer

namespace Slab

def unit (lower : ℝ) : Slab where
  lower
  upper := lower + 1
  increasing := by linarith

end Slab

namespace Drawing

/-- Read only the geometric layers with cells. Connector slabs join
corresponding ports and have no generating boxes. -/
def readSheet : {height : ℝ} → {A B : List O} → Drawing S height A B → Sheet S A B
  | _, A, _, .straight _ _ => .empty A
  | _, _, _, .stack _ layer _ rest => .cons layer.readRow (readSheet rest)

/-- Place successive rows at height intervals of length one, with a
unit-height corridor between each pair. -/
def realize (height : ℝ) : {A B : List O} → Sheet S A B → Drawing S height A B
  | A, _, .empty _ => .straight (Slab.unit height) (Frontier.grid A 1)
  | _, _, .cons row rest =>
    .stack (Slab.unit height) (Layer.realize 0 row)
      (by change height + 1 < height + 2; linarith) (realize (height + 2) rest)

end Drawing
end Silmaril.RuntimeWires.Polygonal
